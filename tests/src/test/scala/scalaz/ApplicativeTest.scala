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

  def compareAndPrintIfDifferent(actual: reflect.runtime.universe.Tree, expected: reflect.runtime.universe.Tree, compareString: Boolean = false) = {
    val areEqual = if(compareString) actual.toString == expected.toString else actual equalsStructure expected
    if (areEqual) true
    else {
      println("ACTUAL PRETTY:\n" + actual)
      println("EXPECTED PRETTY:\n" + expected)
      println("ACTUAL RAW:\n" + showRaw(actual))
      println("EXPECTED RAW:\n" + showRaw(expected))
      false
    }
  }

  def transformLast(ast: reflect.runtime.universe.Tree, nbLines: Int = 1) = {
    val tb = cm.mkToolBox()
    val nameGen = new NameGenerator
    val lastLines = tb.typecheck(ast).children.takeRight(nbLines)
    val testAST = if(nbLines == 1)lastLines.head else Block(lastLines.init, lastLines.last)
    tb.untypecheck(IdiomBracket.transformAST(scala.reflect.runtime.universe, () => nameGen.freshName())(testAST).get)
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

  "Idiom brackets match with extract in lhs" ! forAll { (a: Option[String]) =>
    import IdiomBracket.extract
    val f = IdiomBracket {
      extract(a) match {
        case "hello" => "h"
        case _ => "e"
      }
    }
    if (a.isDefined)
      f == Some(a.get match {
        case "hello" => "h"
        case _ => "e"
      })
    else
      f == None
  }

  /*"Idiom brackets match with extract in case statement" ! forAll { (a: Option[String], b: Option[String]) =>
    import IdiomBracket.extract
    val f = IdiomBracket {
      val bb = extract(b)
      extract(a) match {
        case bb => "h"
        case _ => "e"
      }
    }
    if (a.isDefined)
      f == Some(a.get match {
        case "hello" => "h"
        case _ => "e"
      })
    else
      f == None
  }*/

  "Idiom brackets if statement" ! forAll { (a: Option[String]) =>
    import IdiomBracket.extract
    val f = IdiomBracket {
      if (extract(a).length == 5) 10 else 20
    }
    if (a.isDefined)
      f == Some(if (a.get == 5) 10 else 20)
    else
      f == None
  }

  /*"Idiom bracket like SIP-22 example" ! forAll { (optionDOY: Option[String]) =>
    import IdiomBracket.extract

    val date = """(\d+)/(\d+)""".r
    case class Ok(message: String)
    case class NotFound(message: String)
    def nameOfMonth(num: Int): Option[String] = None

    val f = IdiomBracket {
      extract(optionDOY) match {
        case date(month, day) =>
          Ok(s"It’s ${extract(nameOfMonth(month.toInt))}!")
        case _ =>
          NotFound("Not a date, mate!")
      }
    }
  }*/

  "Idiom bracket in interpolated String" ! forAll {(a: Option[String]) =>
    import IdiomBracket.extract

    val f = IdiomBracket {s"It’s ${extract(a)}!"}
    if (a.isDefined)
      f == Some(s"It’s ${a.get}!")
    else
      f == None
  }

  "Idiom bracket in interpolated String 2" ! forAll {(a: Option[String]) =>
    import IdiomBracket.extract

    case class Ok(message: String)
    def nameOfMonth(num: Int): Option[String] = a
    val month = 5

    val f = IdiomBracket{
      Ok(s"It’s ${extract(nameOfMonth(month.toInt))}!")
    }

    if (a.isDefined)
      f == Some(Ok(s"It’s ${nameOfMonth(month.toInt).get}!"))
    else
      f == None
  }

  /*"Idiom bracket match statement with extractor" ! forAll {(a: Option[List[String]]) =>
    import IdiomBracket.extract

    val f = IdiomBracket.control{
      a.get match {
        case List(one) => one
        case _ => ""
      }
    }

    if (a.isDefined)
      f == Some(a.get match {
        case List(one) => one
        case _ => ""
      })
    else
      f == None
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
                import scalaz.IdiomBracket.extract
                def doThing(a: String, b: String) = ???
                val a: Option[String] = ???
                val b: Option[String] = ???
                doThing(extract(a), extract(b))
              """
    val transformed = transformLast(ast)
    val expected = q"""
                    Applicative[Option].apply2(a,b)(doThing)
                   """
    compareAndPrintIfDifferent(transformed, expected)
  }

  "AST generation complex method invocation" in {
    //IdiomBracket(doThing(extract(a), extract(c).toString).indexOf(b, extract(c)))
    val ast = q"""
                import scalaz.IdiomBracket.extract
                def doThing(a: String, b: String): String = ???
                val a: Option[String] = ???
                val b: Int = ???
                val c: Option[Int] = ???
                doThing(extract(a), extract(c).toString).indexOf(b, extract(c))
              """
    val transformed = transformLast(ast)
    val expected = q"""
                    Applicative[Option].apply3(
                      Applicative[Option].apply2(
                        a,
                        Applicative[Option].map(c)(x4 => x4.toString())
                      )(doThing),
                      Some(b),
                      c
                    )((x1, x2, x3) => x1.indexOf(x2,x3))
                   """
    compareAndPrintIfDifferent(transformed, expected, compareString = true)
  }

  "AST generation recursive" in {
    val ast = q"""
                import scalaz.IdiomBracket.extract
                def doThing(a: String, b: String, c: String): String = ???
                def otherThing(a: String): String = ???
                val a,b,c: Option[String] = ???
                doThing(otherThing(extract(a)),extract(b), extract(c))
              """
    val transformed = transformLast(ast)
    val expected = q"""
                    Applicative[Option].apply3(Applicative[Option].map(a)(otherThing),b,c)(doThing)
                  """
    compareAndPrintIfDifferent(transformed, expected)
  }

  "AST generation with block" in {
    val ast = q"""
                import scalaz.IdiomBracket.extract
                def otherThing(a: String): String = a
                val a: Option[String] = Option("hello")
                val b: Option[String] = Some("h")
                val aa = otherThing(extract(a))
                otherThing(aa)
              """
    val transformed = transformLast(ast, nbLines = 2)
    val expected = q"""
                    {val aa = Applicative[Option].map(a)(otherThing); Applicative[Option].map(aa)(otherThing)}
                   """
    compareAndPrintIfDifferent(transformed, expected)
  }

  "AST generation with double extract" in {
    val ast = q"""
                import scalaz.IdiomBracket.extract
                val a: Option[Option[String]] = ???
                def otherThing(a: String): String = ???
                val aa = otherThing(extract(extract(a)))
                otherThing(aa)
              """
    val transformed = transformLast(ast, nbLines = 2)
    val expected = q"""
                    val aa = Applicative[Option].map(a)(x1 => Applicative[Option].map(x1)(otherThing))
                    Applicative[Option].map(aa)(x2 => Applicative[Option].map(x2)(otherThing))
                   """
    compareAndPrintIfDifferent(transformed, expected, compareString = true)
  }

  "AST generation match with extract in lhs" in {
    val ast = q"""
                import scalaz.IdiomBracket.extract
                val a: Option[String] = ???
                extract(a) match { case "hello" => "h" }
              """
    val transformed = transformLast(ast)
    val expected = q"""
                    Applicative[Option].map(a)(((x1) => x1 match {
                      case "hello" => "h"
                    }))
                   """
    compareAndPrintIfDifferent(transformed, expected, compareString = false)
  }

  "AST generation match with extract in lhs 2" in {
    val ast = q"""
                import scalaz.IdiomBracket.extract
                val a: Option[String] = ???
                extract(a) match {
                  case "hello" => "h"
                  case _ => "e"
                }
              """
    val transformed = transformLast(ast)
    val expected = q"""
                    Applicative[Option].map(a)(((x1) => x1 match {
                      case "hello" => "h"
                      case _ => "e"
                    }))
                   """
    compareAndPrintIfDifferent(transformed, expected, compareString = false)
  }

  /*"AST generation match with deconstructor" in {
    val ast = q"""
                  import scalaz.IdiomBracket.extract
                  val a: Option[List[String]] = ???
                  extract(a) match {
                      case List(one) => one
                      case _ => ""
                  }
              """
    val transformed = transformLast(ast)
    val expected = q"""
                      Applicative[Option].map(a)(((x1) => x1 match {
                        case List(one) => one
                        case _ => "e"
                      }))
                    """
    compareAndPrintIfDifferent(transformed, expected)
  }*/

  "AST generation interpolated string" in {
    val ast = q"""
                import scalaz.IdiomBracket.extract
                val a: Option[String] = ???
                s"It's $${extract(a)}!"
              """
    val transformed = transformLast(ast)
    val expected = q"""
                       Applicative[Option].map(a)(((x1) => scala.StringContext.apply("It\'s ", "!").s(x1)))
                    """
    compareAndPrintIfDifferent(transformed, expected, compareString = true)
  }

  /*"AST generation match with extract in case pattern" in {
    val ast = q
                import scalaz.IdiomBracket.extract
                import scalaz.ApplicativeTest._
                val bb = extract(b)
                extract(a) match {
                  case bb => "h"
                  case _ => "e"
                }

    val tb = cm.mkToolBox()
    val transformed = tb.untypecheck(IdiomBracket.transformAST(scala.reflect.runtime.universe, null)(tb.typecheck(ast)).get)
    val expected = q"""
                    import scalaz.IdiomBracket.extract
                    import scalaz.ApplicativeTest._
                    val bb = b
                    a map {
                      case b if b.map(_ == a).getOrElse(false) => "h"
                      case _ => "e"
                    }
                   """
    compareAndPrintIfDifferent(transformed, expected)
  }*/

  /*"AST generation if statement" in {
    val ast = q"""
                import scalaz.IdiomBracket.extract
                val a: Option[String] = ???
                if (extract(a).length == 5) 10 else 20
              """
    val tb = cm.mkToolBox()
    val nameGen = new NameGenerator
    val lastLine = tb.typecheck(ast).children.last
    val transformed = tb.untypecheck(IdiomBracket.transformAST(scala.reflect.runtime.universe, () => nameGen.freshName())(lastLine).get)
    val expected = q"""
                    Applicative[Option].map(
                      Applicative[Option].map(a)(_.length == 5),
                      Some(10),
                      Some(20)
                    )(if (_) _ else _)
                   """
    compareAndPrintIfDifferent(transformed, expected)
  }*/

  /*"AST generation if statement complex" in {
    val ast = q"""
                import scalaz.IdiomBracket.extract
                val a: Option[String] = ???
                val b: Option[String] = ???
                if (extract(a).length == 5) extract(b) else "hello"
              """
    val tb = cm.mkToolBox()
    val lastLine = tb.typecheck(ast).children.last
    val nameGen = new NameGenerator
    val transformed = tb.untypecheck(IdiomBracket.transformAST(scala.reflect.runtime.universe, () => nameGen.freshName())(lastLine).get)
    val expected = q"""
                    Applicative[Option].map(
                      Applicative[Option].map(a)(_.length == 5),
                      b,
                      Some("hello")
                    )
                    (if (_) _ else _)
                   """
    compareAndPrintIfDifferent(transformed, expected)
  }*/

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
