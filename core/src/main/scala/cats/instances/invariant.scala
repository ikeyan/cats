/*
 * Copyright (c) 2015 Typelevel
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package cats.instances

import cats.kernel._
import cats.kernel.instances.unit._
import cats.{Invariant, InvariantMonoidal, InvariantSemigroupal}

import scala.collection.mutable

trait InvariantMonoidalInstances {
  private class ProductF[A, B, +F[_]](protected val fa: F[A], protected val fb: F[B])
  private trait ProductSemigroup[A, B] extends Semigroup[(A, B)] { this: ProductF[A, B, Semigroup] =>
    def combine(x: (A, B), y: (A, B)): (A, B) = fa.combine(x._1, y._1) -> fb.combine(x._2, y._2)
    final protected def combineIterator(iterator: Iterator[(A, B)]): Option[(A, B)] =
      combineIteratorStack(iterator)
    // groupLen == 16
    // [info] ProductSemigroupBench.semigroup1_100   thrpt    3  207195.359 ± 9202.183  ops/s
    // [info] ProductSemigroupBench.semigroup1_1000  thrpt    3   19913.589 ± 2876.754  ops/s
    // groupLen == 32
    // [info] ProductSemigroupBench.semigroup1_100   thrpt    3  189816.381 ± 10064.868  ops/s
    // [info] ProductSemigroupBench.semigroup1_1000  thrpt    3   21020.265 ±   416.178  ops/s
    final protected def combineIteratorTwoStack(iterator: Iterator[(A, B)]): Option[(A, B)] = {
      val stackA = mutable.ArrayDeque.empty[A]
      val stackB = mutable.ArrayDeque.empty[B]
      var groupLen: Int = 0
      var counter: Long = 1L
      while (iterator.hasNext) {
        val (a, b) = iterator.next()
        stackA.append(a)
        stackB.append(b)
        groupLen += 1
        if (groupLen == 32) {
          val popCount = java.lang.Long.numberOfTrailingZeros(counter)
          val retainCount = stackA.length - popCount - groupLen
          val a = fa.combineAllOption(stackA.view.drop(retainCount)).get
          val b = fb.combineAllOption(stackB.view.drop(retainCount)).get
          stackA.remove(retainCount, popCount + groupLen)
          stackB.remove(retainCount, popCount + groupLen)
          stackA.append(a)
          stackB.append(b)
          groupLen = 0
          counter += 1
        }
      }

      fa.combineAllOption(stackA).zip(fb.combineAllOption(stackB))
    }
    // i < 2
    // i < 4
    // [info] ProductSemigroupBench.semigroup1_100   thrpt    3  421041.396 ± 29834.455  ops/s
    // [info] ProductSemigroupBench.semigroup1_1000  thrpt    3   31470.920 ±   753.273  ops/s
    // i < 8
    // [info] ProductSemigroupBench.semigroup1_100   thrpt    3  358442.388 ± 39662.219  ops/s
    // [info] ProductSemigroupBench.semigroup1_1000  thrpt    3   27414.254 ±  2118.466  ops/s
    // i < 16
    // [info] ProductSemigroupBench.semigroup1_100   thrpt    3  258475.908 ± 16687.226  ops/s
    // [info] ProductSemigroupBench.semigroup1_1000  thrpt    3   21023.486 ±   574.637  ops/s
    final protected def combineIteratorStack(iterator: Iterator[(A, B)]): Option[(A, B)] = {
      val stack = mutable.Stack.empty[(Int, A, B)]

      while (iterator.hasNext) {
        var i = 1
        var (a, b) = iterator.next()
        if (iterator.hasNext) {
          val (a2, b2) = iterator.next()
          i = 2
          a = fa.combine(a, a2)
          b = fb.combine(b, b2)
        }
        while (stack.nonEmpty && stack.top._1 <= i) {
          val top = stack.pop()
          i += top._1
          a = fa.combine(top._2, a)
          b = fb.combine(top._3, b)
        }
        stack.push((i, a, b))
      }

      stack.view.map { case (_, a, b) => (a, b) }.reduceLeftOption(combine)
    }
    final protected def combineIteratorRec(iterator: Iterator[(A, B)]): Option[(A, B)] = {
      def f0: Option[(A, B)] = iterator.nextOption()
      def f1: Option[(A, B)] = {
        iterator.nextOption().map { pair =>
          var (a, b) = pair
          iterator.nextOption()
        }
      }
      def f1(a: A, b: B): (A, B) = {
        val (a1, b1) = f0(a, b)
        f0()
      }
      def f(maxDepth: Int): Option[(A, B)] = {
        for (d <- 0 until maxDepth) {
          f(d) match {
            case None        => return
            case Some(value) => ???
          }
        }
      }
    }
    // [info] ProductSemigroupBench.semigroup1_100   thrpt    3  209489.181 ± 27372.488  ops/s
    // [info] ProductSemigroupBench.semigroup1_1000  thrpt    3   17714.666 ±  1886.205  ops/s
    final protected def combineIteratorNew(iterator: Iterator[(A, B)]): Option[(A, B)] = {
      val stack = mutable.Stack.empty[(Int, A, B)]
      val queueA = mutable.ArrayDeque.empty[A]
      val queueB = mutable.ArrayDeque.empty[B]

      while (iterator.hasNext) {
        val (a, b) = iterator.next()
        queueA.append(a)
        queueB.append(b)
        if (queueA.size == 16) {
          var totalCount = 16
          while (stack.nonEmpty && stack.top._1 <= totalCount) {
            val top = stack.pop()
            queueA.prepend(top._2)
            queueB.prepend(top._3)
            totalCount += top._1
          }
          val a = fa.combineAllOption(queueA).get
          val b = fb.combineAllOption(queueB).get
          queueA.clear()
          queueB.clear()
          stack.push((totalCount, a, b))
        }
      }
      while (stack.nonEmpty) {
        val top = stack.pop()
        queueA.prepend(top._2)
        queueB.prepend(top._3)
      }
      fa.combineAllOption(queueA).zip(fb.combineAllOption(queueB))
    }
    final override def combineAllOption(as: IterableOnce[(A, B)]): Option[(A, B)] = as match {
      case iterable: Iterable[(A, B)] =>
        fa.combineAllOption(iterable.map(_._1)).zip(fb.combineAllOption(iterable.map(_._2)))
      case _ => combineIterator(as.iterator)
    }
  }
  private trait ProductMonoid[A, B] extends Monoid[(A, B)] with ProductSemigroup[A, B] { this: ProductF[A, B, Monoid] =>
    final val empty: (A, B) = fa.empty -> fb.empty
    override def combineAll(as: IterableOnce[(A, B)]): (A, B) = as match {
      case iterable: Iterable[(A, B)] => (fa.combineAll(iterable.map(_._1)), fb.combineAll(iterable.map(_._2)))
      case _                          => combineIterator(as.iterator).getOrElse(empty)
    }
  }

  private class ImapF[A, B, +F[_]](protected val fa: F[A])(protected val f: A => B)(protected val g: B => A)
  private trait ImapSemigroup[A, B] extends Semigroup[B] { this: ImapF[A, B, Semigroup] =>
    def combine(x: B, y: B): B = f(fa.combine(g(x), g(y)))
    override def combineN(a: B, n: Int): B = f(fa.combineN(g(a), n))
    override def combineAllOption(as: IterableOnce[B]): Option[B] = fa.combineAllOption(as.iterator.map(g)).map(f)
  }
  private trait ImapMonoid[A, B] extends Monoid[B] with ImapSemigroup[A, B] { this: ImapF[A, B, Monoid] =>
    def empty: B = f(fa.empty)
    override def combineAll(as: IterableOnce[B]): B = f(fa.combineAll(as.iterator.map(g)))
  }

  implicit def catsSemigroupalForMonoid: InvariantSemigroupal[Monoid] =
    new InvariantSemigroupal[Monoid] {
      def product[A, B](fa: Monoid[A], fb: Monoid[B]): Monoid[(A, B)] =
        new ProductF[A, B, Monoid](fa, fb) with ProductMonoid[A, B]
      def imap[A, B](fa: Monoid[A])(f: A => B)(g: B => A): Monoid[B] =
        new ImapF[A, B, Monoid](fa)(f)(g) with ImapMonoid[A, B]
    }
  implicit val catsInvariantMonoidalSemigroup: InvariantMonoidal[Semigroup] = new InvariantMonoidal[Semigroup] {
    def product[A, B](fa: Semigroup[A], fb: Semigroup[B]): Semigroup[(A, B)] =
      new ProductF[A, B, Semigroup](fa, fb) with ProductSemigroup[A, B]
    def imap[A, B](fa: Semigroup[A])(f: A => B)(g: B => A): Semigroup[B] =
      new ImapF[A, B, Semigroup](fa)(f)(g) with ImapSemigroup[A, B]

    def unit: Semigroup[Unit] = implicitly
  }

  implicit val catsInvariantMonoidalCommutativeSemigroup: InvariantMonoidal[CommutativeSemigroup] =
    new InvariantMonoidal[CommutativeSemigroup] {
      def product[A, B](fa: CommutativeSemigroup[A], fb: CommutativeSemigroup[B]): CommutativeSemigroup[(A, B)] =
        new ProductF[A, B, CommutativeSemigroup](fa, fb) with CommutativeSemigroup[(A, B)] with ProductSemigroup[A, B]

      def imap[A, B](fa: CommutativeSemigroup[A])(f: A => B)(g: B => A): CommutativeSemigroup[B] =
        new ImapF[A, B, CommutativeSemigroup](fa)(f)(g) with CommutativeSemigroup[B] with ImapSemigroup[A, B]

      def unit: CommutativeSemigroup[Unit] = implicitly
    }
}

trait InvariantInstances {
  implicit val catsInvariantForNumeric: Invariant[Numeric] = new Invariant[Numeric] {
    def imap[A, B](fa: Numeric[A])(f: A => B)(g: B => A): Numeric[B] =
      new ScalaVersionSpecificNumeric[A, B](fa)(f)(g) {}
  }

  implicit val catsInvariantForIntegral: Invariant[Integral] = new Invariant[Integral] {
    def imap[A, B](fa: Integral[A])(f: A => B)(g: B => A): Integral[B] =
      new ScalaVersionSpecificNumeric[A, B](fa)(f)(g) with Integral[B] {
        override def quot(x: B, y: B): B = f(fa.quot(g(x), g(y)))
        override def rem(x: B, y: B): B = f(fa.rem(g(x), g(y)))
      }
  }
}

trait InvariantInstancesBinCompat0 {
  implicit val catsInvariantForFractional: Invariant[Fractional] = new Invariant[Fractional] {
    def imap[A, B](fa: Fractional[A])(f: A => B)(g: B => A): Fractional[B] =
      new ScalaVersionSpecificNumeric[A, B](fa)(f)(g) with Fractional[B] {
        override def div(x: B, y: B): B = f(fa.div(g(x), g(y)))
      }
  }
}
