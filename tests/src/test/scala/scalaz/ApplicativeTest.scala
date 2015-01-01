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
  val a1 = Some(Some("hello"))

  class NameGenerator {
    var number = 0
    def freshName() = {
      number += 1
      "x" + number
    }
  }

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

  "Idiom brackets with really complex method invocation" ! forAll { (a: Option[String], b: Int, c: Option[Int]) =>
    import IdiomBracket.extract
    val f = IdiomBracket(doThing(extract(a), extract(c).toString).indexOf(b, extract(c)))
    if (a.isDefined && c.isDefined)
      f == Some(a.get.indexOf(b, c.get))
    else
      f == None
  }

  "Idiom brackets with complex method invocation" ! forAll { (a: Option[String], b: Int, c: Option[Int], d: Option[String]) =>
    import IdiomBracket.extract
    val f = IdiomBracket(doThing(extract(a), extract(d)).indexOf(b, extract(c)))
    if (a.isDefined && c.isDefined && d.isDefined)
      f == Some(doThing(a.get, d.get).indexOf(b, c.get))
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

  "Idiom brackets with double extract" ! forAll { (a: Option[Option[String]]) =>
    import IdiomBracket.extract
    def otherThing(ff: String) = ff * 3
    val f = IdiomBracket.apply2{
      val aa = otherThing(extract(extract(a)))
      otherThing(aa)
    }
    if (a.isDefined && a.get.isDefined)
      f == Some(Some(otherThing(otherThing(a.get.get))))
    else if(a.isDefined)
      f == Some(None)
    else
      f == None
  }

  /*"Idiom bracket like SIP-22 example" ! forAll { (optionDOY: Option[String]) =>
    import IdiomBracket.extract

    val date = """(\d+)/(\d+)""".r
    case class Ok(message: String)
    case class NotFound(message: String)
    def nameOfMonth(num: Int): Option[String] = None

    IdiomBracket {
      extract(optionDOY) match {
        case date(month, day) =>
          Ok(s"It’s ${extract(nameOfMonth(month.toInt))}!")
        case _ =>
          NotFound("Not a date, mate!")
      }
    }
  }*/

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
    val transformed = tb.untypecheck(IdiomBracket.transformAST(scala.reflect.runtime.universe, null)(tb.typecheck(ast)).get)
    val expected = q"""
                    import scalaz._
                    Applicative[Option].apply2(scalaz.ApplicativeTest.a,scalaz.ApplicativeTest.b)(scalaz.ApplicativeTest.doThing)
                   """
    if(transformed equalsStructure expected) true else {println(transformed);println(showRaw(transformed)); println(expected);println(showRaw(expected)); false}
  }

  "AST generation complex method invocation" in {
    //IdiomBracket(doThing(extract(a), extract(c).toString).indexOf(b, extract(c)))
    val ast = q"""
                import scalaz._
                val a: Option[String] = ???
                val b: Int = ???
                val c: Option[Int] = ???
                ApplicativeTest.doThing(IdiomBracket.extract(a), IdiomBracket.extract(c).toString).indexOf(b, IdiomBracket.extract(c))
              """
    val tb = cm.mkToolBox()
    val testAST = tb.typecheck(ast).children.last
    val nameGen = new NameGenerator
    val transformed = tb.untypecheck(IdiomBracket.transformAST(scala.reflect.runtime.universe, () => nameGen.freshName())(testAST).get)
    val expected = q"""
                    Applicative[Option].apply3(
                      Applicative[Option].apply2(
                        a,
                        Applicative[Option].map(c)(x4 => x4.toString())
                      )(scalaz.ApplicativeTest.doThing),
                      Some(b),
                      c
                    )((x1, x2, x3) => x1.indexOf(x2,x3))
                   """
    if(transformed.toString equals expected.toString) true else {println("TRANSFORMED PRETTY:\n" + transformed);println("EXPECTED PRETTY:\n" + expected);println("TRANSFORMED RAW:\n" + showRaw(transformed));println("EXPECTED RAW:\n" + showRaw(expected)); false}
  }

  "AST generation recursive" in {
    val ast = q"""
                import scalaz._
                ApplicativeTest.doThing(ApplicativeTest.otherThing(IdiomBracket.extract(ApplicativeTest.a)),IdiomBracket.extract(ApplicativeTest.b), IdiomBracket.extract(ApplicativeTest.c))
              """
    val tb = cm.mkToolBox()
    val transformed = tb.untypecheck(IdiomBracket.transformAST(scala.reflect.runtime.universe, null)(tb.typecheck(ast)).get)
    val expected = q"""
                    import scalaz._
                    Applicative[Option].apply3(Applicative[Option].map(scalaz.ApplicativeTest.a)(scalaz.ApplicativeTest.otherThing),scalaz.ApplicativeTest.b,scalaz.ApplicativeTest.c)(scalaz.ApplicativeTest.doThing)
                  """
    if(transformed equalsStructure expected) true else {println(transformed);println(showRaw(transformed)); println(expected);println(showRaw(expected)); false}
  }

  "AST generation with block" in {
    val ast = q"""
                import scalaz.IdiomBracket.extract
                import scalaz.ApplicativeTest._
                {val aa = otherThing(extract(a)); otherThing(aa)}
              """
    val tb = cm.mkToolBox()
    val transformed = tb.untypecheck(IdiomBracket.transformAST(scala.reflect.runtime.universe, null)(tb.typecheck(ast)).get)
    val expected = q"""
                    import scalaz.IdiomBracket.extract
                    import scalaz.ApplicativeTest._
                    {val aa = Applicative[Option].map(scalaz.ApplicativeTest.a)(scalaz.ApplicativeTest.otherThing); Applicative[Option].map(aa)(scalaz.ApplicativeTest.otherThing)}
                   """
    if(transformed equalsStructure expected) true else {println(transformed);println(showRaw(transformed)); println(expected);println(showRaw(expected)); false}
  }

  "AST generation with double extract" in {
    val ast = q"""
                import scalaz.IdiomBracket.extract
                import scalaz.ApplicativeTest._
                val aa = otherThing(extract(extract(a1)))
                otherThing(aa)
              """
    val tb = cm.mkToolBox()
    val nameGen = new NameGenerator
    val rawTransformed = tb.untypecheck(IdiomBracket.transformAST(scala.reflect.runtime.universe, () => nameGen.freshName())(tb.typecheck(ast)).get)
    val minusTwoImports = rawTransformed.children.drop(2)
    val transformed = Block(minusTwoImports.init, minusTwoImports.last)
    val expected = q"""
                    val aa = Applicative[Option].map(scalaz.ApplicativeTest.a1)(x1 => Applicative[Option].map(x1)(scalaz.ApplicativeTest.otherThing))
                    Applicative[Option].map(aa)(x2 => Applicative[Option].map(x2)(scalaz.ApplicativeTest.otherThing))
                   """
    if(transformed.toString == expected.toString) true else {println(transformed);println(showRaw(transformed)); println(expected);println(showRaw(expected)); false}
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
