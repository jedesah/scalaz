package scalaz

import org.scalacheck.{Prop, Gen}
import org.scalacheck.Prop.forAll

import scala.reflect.runtime.universe._
import scala.reflect.runtime.{currentMirror => cm}
import scala.tools.reflect.ToolBox

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

  def doThing(a: String) = a * 3
  def doThing(a: String, b: String) = a + b
  def doThing(a: String, b: String, c: String) = a + b + c
  def otherThing(a: String) = a * 2
  val a = Some("hello")
  val b = Some("hello1")
  val c = Some("hello2")

  "replicateM is the same" ! forAll { (fa: Option[Int]) => forAll(Gen.choose(0, 100)) { n =>
    fa.replicateM(n) must_===(replicateM(n, fa))
  }}

  "filterM is the same" ! forAll { (l: List[Int]) =>
    // don't make `None` too likely
    def pred(n: Int) = if (n < 0 && n % 2 == 0) None else Some(n % 2 == 0)
    l.filterM(pred) must_===(filterM(l, pred))
  }

  "Idiom brackets with 2 params" ! forAll { (a: Option[String], b: Option[String]) =>
    import IdiomBracket.extract
    def doThing(e: String, f: String) = e + f
    val f = IdiomBracket(doThing(extract(a),extract(b)))
    if (a.isDefined && b.isDefined)
      f == Some(doThing(a.get, b.get))
    else
      f == None
  }

  "Idiom brackets with renamed import" ! forAll { (a: Option[String], b: Option[String]) =>
    import IdiomBracket.{extract => extractt}
    def doThing(e: String, f: String) = e + f
    val f = IdiomBracket(doThing(extractt(a),extractt(b)))
    if (a.isDefined && b.isDefined)
      f == Some(doThing(a.get, b.get))
    else
      f == None
  }

  "Idiom brackets with implicit extract" ! forAll { (a: Option[String], b: Option[String]) =>
    import IdiomBracket.auto.extract
    def doThing(e: String, f: String) = e + f
    val f = IdiomBracket(doThing(a,b))
    if (a.isDefined && b.isDefined)
      f == Some(doThing(a.get, b.get))
    else
      f == None
  }

  "Idiom brackets with 3 params" ! forAll { (a: Option[String], b: Option[String], c: Option[String]) =>
    import IdiomBracket.extract
    def doThing(e: String, f: String, h: String) = e + f + h
    val f = IdiomBracket(doThing(extract(a),extract(b), extract(c)))
    if (a.isDefined && b.isDefined && c.isDefined)
      f == Some(doThing(a.get, b.get, c.get))
    else
      f == None
  }

  "Idiom brackets with mixed params" ! forAll { (a: String, b: Option[String], c: Option[String]) =>
    import IdiomBracket.extract
    def doThing(e: String, f: String, h: String) = e + f + h
    val f = IdiomBracket(doThing(a,extract(b), extract(c)))
    if (b.isDefined && c.isDefined)
      f == Some(doThing(a, b.get, c.get))
    else
      f == None
  }

  "Idiom brackets with method invocation" ! forAll { (a: String, b: Option[Int], c: Option[Int]) =>
    import IdiomBracket.extract
    val f = IdiomBracket(a.indexOf(extract(b), extract(c)))
    if (b.isDefined && c.isDefined)
      f == Some(a.indexOf(b.get, c.get))
    else
      f == None
  }

  "Idiom brackets with method invocation different" ! forAll { (a: Option[String], b: Int, c: Option[Int]) =>
    import IdiomBracket.extract
    val f = IdiomBracket(extract(a).indexOf(b, extract(c)))
    if (a.isDefined && c.isDefined)
      f == Some(a.get.indexOf(b, c.get))
    else
      f == None
  }

  "Idiom brackets with extract within argument" ! forAll { (a: Option[String], b: Option[String], c: Option[String]) =>
    import IdiomBracket.extract
    def doThing(e: String, f: String, h: String) = e + f + h
    def otherThing(ff: String) = ff * 3
    val f = IdiomBracket(doThing(otherThing(extract(a)),extract(b), extract(c)))
    if (a.isDefined && b.isDefined && c.isDefined)
      f == Some(doThing(otherThing(a.get), b.get, c.get))
    else
      f == None
  }

  "Idiom brackets with deeply nested extract within argument" ! forAll { (a: Option[String], b: Option[String], c: Option[String]) =>
    import IdiomBracket.extract
    def doThing(e: String, f: String, h: String) = e + f + h
    def otherThing(ff: String) = ff * 3
    def firstThis(gg: String) = gg.take(1)
    val f = IdiomBracket(doThing(otherThing(firstThis(extract(a))),extract(b), extract(c)))
    if (a.isDefined && b.isDefined && c.isDefined)
      f == Some(doThing(otherThing(firstThis(a.get)), b.get, c.get))
    else
      f == None
  }

  "Idiom brackets with simple block" ! forAll { (a: Option[String]) =>
    import IdiomBracket.extract
    def otherThing(ff: String) = ff * 3
    val f = IdiomBracket {
      otherThing(extract(a))
    }
    if (a.isDefined)
      f == Some(otherThing(a.get))
    else
      f == None
  }

  "Idiom brackets with simple useless block" ! forAll { (a: Option[String]) =>
    import IdiomBracket.extract
    def otherThing(ff: String) = ff * 3
    val f = IdiomBracket {
      otherThing(extract(a))
      otherThing(extract(a))
    }
    if (a.isDefined)
      f == Some(otherThing(a.get))
    else
      f == None
  }

  "Idiom brackets with block with pointless val" ! forAll { (a: Option[String]) =>
    import IdiomBracket.extract
    def otherThing(ff: String) = ff * 3
    val f = IdiomBracket {
      val aa = otherThing(extract(a))
      aa
    }
    if (a.isDefined)
      f == Some(otherThing(a.get))
    else
      f == None
  }

  "Idiom brackets with block" ! forAll { (a: Option[String]) =>
    import IdiomBracket.extract
    def otherThing(ff: String) = ff * 3
    val f = IdiomBracket {
      val aa = otherThing(extract(a))
      otherThing(aa)
    }
    if (a.isDefined)
      f == Some(otherThing(otherThing(a.get)))
    else
      f == None
  }

  "extract does not compile on it's own" in {
    val ast = q"""
                import scalaz._
                ApplicativeTest.doThing(IdiomBracket.extract(ApplicativeTest.a))
              """
    val tb = cm.mkToolBox()
    tb.compile(ast).mustThrowA[scala.tools.reflect.ToolBoxError]
  }

  "AST generation" in {
    val ast = q"""
                import scalaz._
                ApplicativeTest.doThing(IdiomBracket.extract(ApplicativeTest.a), IdiomBracket.extract(ApplicativeTest.b))
              """
    val tb = cm.mkToolBox()
    val transformed = tb.untypecheck(IdiomBracket.transformAST(scala.reflect.runtime.universe)(tb.typecheck(ast)))
    val expected = q"""
                    import scalaz._
                    Applicative[Option].apply2(scalaz.ApplicativeTest.a,scalaz.ApplicativeTest.b)(scalaz.ApplicativeTest.doThing)
                   """
    if(transformed equalsStructure expected) true else {println(transformed);println(showRaw(transformed)); println(expected);println(showRaw(expected)); false}
  }

  "AST generation recursive" in {
    val ast = q"""
                import scalaz._
                ApplicativeTest.doThing(ApplicativeTest.otherThing(IdiomBracket.extract(ApplicativeTest.a)),IdiomBracket.extract(ApplicativeTest.b), IdiomBracket.extract(ApplicativeTest.c))
              """
    val tb = cm.mkToolBox()
    val transformed = tb.untypecheck(IdiomBracket.transformAST(scala.reflect.runtime.universe)(tb.typecheck(ast)))
    val expected = q"""
                    import scalaz._
                    Applicative[Option].apply3(Applicative[Option].map(scalaz.ApplicativeTest.a)(scalaz.ApplicativeTest.otherThing),scalaz.ApplicativeTest.b,scalaz.ApplicativeTest.c)(scalaz.ApplicativeTest.doThing)
                  """
    if(transformed equalsStructure expected) true else {println(transformed);println(showRaw(transformed)); println(expected);println(showRaw(expected)); false}
  }

  // TODO: Update this test to be typechecked and maybe understand better why this one works and the other ones didn't
  "AST generation with block" in {
    val ast = q"{val aa = otherThing(extract(a)); otherThing(aa)}"
    val transformed = IdiomBracket.transformAST(scala.reflect.runtime.universe)(ast)
    val expected = q"{val aa = Applicative[Option].map(a)(otherThing); Applicative[Option].map(aa)(otherThing)}"
    if(transformed equalsStructure expected) true else {println(transformed);println(showRaw(transformed)); println(expected);println(showRaw(expected)); false}
  }

  "assumption" ! forAll { (a: Option[String], b: Option[String]) =>
    def doThing(a: String, b: String) = a + b
    val f = Applicative[Option].apply2(a,b)(doThing)
    if (a.isDefined && b.isDefined)
      f == Some(doThing(a.get,b.get))
    else
      f == None
  }

  "assumption recursive" ! forAll { (a: Option[String], b: Option[String], c: Option[String]) =>
    def doThing(a: String, b: String, c: String) = a + b + c
    def otherThing(ff: String) = ff * 3
    val f = Applicative[Option].apply3(Applicative[Option].map(a)(otherThing),b,c)(doThing)
    if (a.isDefined && b.isDefined && c.isDefined)
      f == Some(doThing(otherThing(a.get),b.get, c.get))
    else
      f == None
  }

  "assumption method call" ! forAll { (a: String, b: Option[Int], c: Option[Int]) =>
    val f = Applicative[Option].apply3(Some(a),b,c)(_.indexOf(_,_))
    if (b.isDefined && c.isDefined)
      f == Some(a.indexOf(b.get, c.get))
    else
      f == None
  }

  "assumption block" ! forAll { (a: Option[String]) =>
    def otherThing(ff: String) = ff * 3
    val f = {
      val aa = Applicative[Option].map(a)(otherThing)
      Applicative[Option].map(aa)(otherThing)
    }
    if (a.isDefined)
      f == Some(otherThing(otherThing(a.get)))
    else
      f == None
  }

}

// vim: expandtab:ts=2:sw=2
