package scalaz

import org.scalacheck.{Prop, Gen}
import org.scalacheck.Prop.forAll

import scala.reflect.runtime.universe._

object ApplicativeTest extends SpecLite {

  // In c44c206461fe, the functions `replicateM`, `replicateM_`, `filterM`
  // and `partitionM` have been generalized from `Monad` to `Applicative`.
  // We compare the old with the new implementation here.

  import std.list._
  import std.option._
  import std.anyVal._
  import syntax.std.list._
  import syntax.applicative._

  def replicateM[F[_] : Monad, A](n: Int, fa: F[A]): F[List[A]] =
    listInstance.sequence(List.fill(n)(fa))

  def filterM[F[_] : Monad, A](l: List[A], f: A => F[Boolean]): F[List[A]] =
    l match {
      case Nil => Monad[F].point(List())
      case h :: t => Monad[F].bind(f(h))(b => Monad[F].map(filterM(t, f))(t => if (b) h :: t else t))
    }

  "replicateM is the same" ! forAll { (fa: Option[Int]) => forAll(Gen.choose(0, 100)) { n =>
    fa.replicateM(n) must_===(replicateM(n, fa))
  }}

  "filterM is the same" ! forAll { (l: List[Int]) =>
    // don't make `None` too likely
    def pred(n: Int) = if (n < 0 && n % 2 == 0) None else Some(n % 2 == 0)
    l.filterM(pred) must_===(filterM(l, pred))
  }

  "Idiom brackets" ! forAll { (a: Option[String], b: Option[String]) =>
    import IdiomBracket.extract
    def doThing(e: String, f: String) = e + f
    val f = IdiomBracket(doThing(extract(a),extract(b)))
    if (a.isDefined && b.isDefined)
      f == Some(a.get + b.get)
    else
      f == None
  }

  "AST generation" in {
    val ast = q"doThing(extract(a), extract(b))"
    val transformed = IdiomBracket.transformAST(scala.reflect.runtime.universe)(ast)
    val expected = q"Applicative[Option].apply2(a,b)(doThing)"
    if(transformed equalsStructure expected) true else {println(showRaw(transformed)); println(showRaw(expected)); false}
  }

  "assumption" ! forAll { (a: Option[String], b: Option[String]) =>
    def doThing(a: String, b: String) = a + b
    val f = Applicative[Option].apply2(a,b)(doThing)
    if (a.isDefined && b.isDefined)
      f == Some(a.get + b.get)
    else
      f == None
  }

}

// vim: expandtab:ts=2:sw=2
