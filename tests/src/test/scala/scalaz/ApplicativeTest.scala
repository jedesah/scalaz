package scalaz

import org.scalacheck.{Arbitrary, Prop, Gen}
import Arbitrary.arbitrary
import org.scalacheck.Prop.forAll

import scala.concurrent.Await
import scala.concurrent.Promise
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

  implicit def FutureArbitrary[A: Arbitrary]: Arbitrary[scala.concurrent.Future[A]] =
    Arbitrary(arbitrary[A] map ((x: A) => scala.concurrent.Future.successful(x)))

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

  def transformLast(ast: reflect.runtime.universe.Tree, nbLines: Int = 1, monadic: Boolean = false) = {
    val tb = cm.mkToolBox()
    val nameGen = new NameGenerator
    val lastLines = tb.typecheck(ast).children.takeRight(nbLines)
    val testAST = if(nbLines == 1)lastLines.head else Block(lastLines.init, lastLines.last)
    tb.untypecheck(IdiomBracket.transformAST(scala.reflect.runtime.universe, () => nameGen.freshName())(testAST, q"App", monadic).get)
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
    val f = IdiomBracket[Option, String](doThing(extract[Option, String](a),extract[Option, String](b)))
    if (a.isDefined && b.isDefined)
      f == Some(doThing(a.get, b.get))
    else
      f == None
  }

  "Idiom brackets with renamed import" ! forAll { (a: Option[String], b: Option[String]) =>
    import IdiomBracket.{extract => extractt}
    def doThing(e: String, f: String) = e + f
    val f = IdiomBracket[Option, String](doThing(extractt(a),extractt(b)))
    if (a.isDefined && b.isDefined)
      f == Some(doThing(a.get, b.get))
    else
      f == None
  }

  "Idiom brackets with implicit extract" ! forAll { (a: Option[String], b: Option[String]) =>
    import IdiomBracket.auto.extract
    def doThing(e: String, f: String) = e + f
    val f = IdiomBracket[Option, String](doThing(a,b))
    if (a.isDefined && b.isDefined)
      f == Some(doThing(a.get, b.get))
    else
      f == None
  }

  "Idiom brackets with 3 params" ! forAll { (a: Option[String], b: Option[String], c: Option[String]) =>
    import IdiomBracket.extract
    def doThing(e: String, f: String, h: String) = e + f + h
    val f = IdiomBracket[Option, String](doThing(extract(a),extract(b), extract(c)))
    if (a.isDefined && b.isDefined && c.isDefined)
      f == Some(doThing(a.get, b.get, c.get))
    else
      f == None
  }

  "Idiom brackets with mixed params" ! forAll { (a: String, b: Option[String], c: Option[String]) =>
    import IdiomBracket.extract
    def doThing(e: String, f: String, h: String) = e + f + h
    val f = IdiomBracket[Option, String](doThing(a,extract(b), extract(c)))
    if (b.isDefined && c.isDefined)
      f == Some(doThing(a, b.get, c.get))
    else
      f == None
  }

  "Idiom brackets with method invocation" ! forAll { (a: String, b: Option[Int], c: Option[Int]) =>
    import IdiomBracket.extract
    val f = IdiomBracket[Option, Int](a.indexOf(extract(b), extract(c)))
    if (b.isDefined && c.isDefined)
      f == Some(a.indexOf(b.get, c.get))
    else
      f == None
  }

  "Idiom brackets with method invocation different" ! forAll { (a: Option[String], b: Int, c: Option[Int]) =>
    import IdiomBracket.extract
    val f = IdiomBracket[Option, Int](extract(a).indexOf(b, extract(c)))
    if (a.isDefined && c.isDefined)
      f == Some(a.get.indexOf(b, c.get))
    else
      f == None
  }

  "Idiom brackets with really complex method invocation" ! forAll { (a: Option[String], b: Int, c: Option[Int]) =>
    import IdiomBracket.extract
    val f = IdiomBracket[Option, Int](doThing(extract(a), extract(c).toString).indexOf(b, extract(c)))
    if (a.isDefined && c.isDefined)
      f == Some(a.get.indexOf(b, c.get))
    else
      f == None
  }

  "Idiom brackets with complex method invocation" ! forAll { (a: Option[String], b: Int, c: Option[Int], d: Option[String]) =>
    import IdiomBracket.extract
    val f = IdiomBracket[Option, Int](doThing(extract(a), extract(d)).indexOf(b, extract(c)))
    if (a.isDefined && c.isDefined && d.isDefined)
      f == Some(doThing(a.get, d.get).indexOf(b, c.get))
    else
      f == None
  }

  "Idiom brackets with extract within argument" ! forAll { (a: Option[String], b: Option[String], c: Option[String]) =>
    import IdiomBracket.extract
    def doThing(e: String, f: String, h: String) = e + f + h
    def otherThing(ff: String) = ff * 3
    val f = IdiomBracket[Option, String](doThing(otherThing(extract(a)),extract(b), extract(c)))
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
    val f = IdiomBracket[Option, String](doThing(otherThing(firstThis(extract(a))),extract(b), extract(c)))
    if (a.isDefined && b.isDefined && c.isDefined)
      f == Some(doThing(otherThing(firstThis(a.get)), b.get, c.get))
    else
      f == None
  }

  "Idiom brackets with simple block" ! forAll { (a: Option[String]) =>
    import IdiomBracket.extract
    def otherThing(ff: String) = ff * 3
    val f = IdiomBracket[Option, String] {
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
    val f = IdiomBracket[Option, String] {
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
    val f = IdiomBracket[Option, String] {
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
    val f = IdiomBracket[Option, String] {
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
    val f = IdiomBracket[Option, String] {
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

  "Idiom brackets match with stable identifier in case statement" ! forAll { (a: Option[String], b: Option[String]) =>
    import IdiomBracket.extract
    val f = IdiomBracket[Option, String] {
      val bb = extract(b)
      extract(a) match {
        case `bb` => "h"
        case _ => "e"
      }
    }
    val expected = Applicative[Option].apply2(a,b)((a,b) =>
      a match {
        case `b` => "h"
        case _ => "e"
      }
    )
    f == expected
  }

  "Idiom brackets if statement" ! forAll { (a: Option[String]) =>
    import IdiomBracket.extract
    val f = IdiomBracket[Option, Int] {
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

    val f = IdiomBracket[Option, String] {s"It’s ${extract(a)}!"}
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

    val f = IdiomBracket[Option, Ok]{
      Ok(s"It’s ${extract(nameOfMonth(month.toInt))}!")
    }

    if (a.isDefined)
      f == Some(Ok(s"It’s ${nameOfMonth(month.toInt).get}!"))
    else
      f == None
  }

  "Idiom bracket with List" ! forAll {(a: List[String], b: List[String]) =>
    import IdiomBracket.extract

    val f = IdiomBracket[List, String](extract(a) + extract(b))

    f == Applicative[List].apply2(a,b)(_ + _)
  }

  "Idiom bracket with Future" ! forAll {(a: scala.concurrent.Future[String], b: scala.concurrent.Future[String]) =>
    import IdiomBracket.extract
    import scala.concurrent.Future
    import scala.concurrent.ExecutionContext.Implicits.global
    import scala.concurrent.duration._

    implicit val applicative: Applicative[Future] = scalaz.std.scalaFuture.futureInstance

    val f = IdiomBracket[Future, String](extract(a) + extract(b))

    Await.result(f, 100.milliseconds) == Await.result(Applicative[Future].apply2(a,b)(_ + _), 100.milliseconds)
  }

  "Idiom bracket monad in interpolated String" ! forAll {(a: Option[String]) =>
    import IdiomBracket.extract

    val f = IdiomBracket.monad[Option, String] {s"It’s ${extract(a)}!"}
    if (a.isDefined)
      f == Some(s"It’s ${a.get}!")
    else
      f == None
  }

  "Idiom bracket monad is lazy with if/else" in {
    import IdiomBracket.extract
    import scala.concurrent.Future
    import scala.concurrent.Promise
    import scala.concurrent.ExecutionContext.Implicits.global
    import scala.concurrent.duration._

    val aPromise = Promise[Boolean]()
    val a = aPromise.future

    val bPromise = Promise[String]()
    val b = bPromise.future

    val cPromise = Promise[String]()
    val c = cPromise.future

    implicit val monad: Monad[Future] = scalaz.std.scalaFuture.futureInstance

    val f = IdiomBracket.monad[Future, String](if(extract(a)) extract(b) else extract(c))

    f.value == None

    aPromise.success(true)

    f.value == None

    bPromise.success("hello")

    Await.result(f, 1.second) == "hello"
  }

  /*"Idiom bracket match statement with unapply" ! forAll {(a: Option[List[String]]) =>
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

  /*"Idiom bracket match statement with case class unapply" ! forAll {(a: Option[String]) =>
    import IdiomBracket.extract

    case class Ok(a: String)

    val ok = a.map(Ok(_))

    val f = IdiomBracket{
      extract(ok) match {
        case Ok(inside) => inside
        case _ => ""
      }
    }

    if (a.isDefined)
      f == Some(ok.get match {
        case Ok(inside) => inside
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
                import scalaz.IdiomBracket.auto.extract
                def doThing(a: String, b: String) = ???
                val a: Option[String] = ???
                val b: Option[String] = ???
                doThing(extract(a), extract(b))
              """
    val transformed = transformLast(ast)
    val expected = q"""
                    App.apply2(a,b)(doThing)
                   """
    compareAndPrintIfDifferent(transformed, expected)
  }

  "AST generation complex method invocation" in {
    //IdiomBracket(doThing(extract(a), extract(c).toString).indexOf(b, extract(c)))
    val ast = q"""
                import scalaz.IdiomBracket.auto.extract
                def doThing(a: String, b: String): String = ???
                val a: Option[String] = ???
                val b: Int = ???
                val c: Option[Int] = ???
                doThing(extract(a), extract(c).toString).indexOf(b, extract(c))
              """
    val transformed = transformLast(ast)
    val expected = q"""
                    App.apply3(
                      App.apply2(
                        a,
                        App.map(c)(x4 => x4.toString())
                      )(doThing),
                      App.pure(b),
                      c
                    )((x1, x2, x3) => x1.indexOf(x2,x3))
                   """
    compareAndPrintIfDifferent(transformed, expected, compareString = true)
  }

  "AST generation recursive" in {
    val ast = q"""
                import scalaz.IdiomBracket.auto.extract
                def doThing(a: String, b: String, c: String): String = ???
                def otherThing(a: String): String = ???
                val a,b,c: Option[String] = ???
                doThing(otherThing(extract(a)),extract(b), extract(c))
              """
    val transformed = transformLast(ast)
    val expected = q"""
                    App.apply3(App.map(a)(otherThing),b,c)(doThing)
                  """
    compareAndPrintIfDifferent(transformed, expected)
  }

  "AST generation with block" in {
    val ast = q"""
                import scalaz.IdiomBracket.auto.extract
                def otherThing(a: String): String = a
                val a: Option[String] = Option("hello")
                val b: Option[String] = Some("h")
                val aa = otherThing(extract(a))
                otherThing(aa)
              """
    val transformed = transformLast(ast, nbLines = 2)
    val expected = q"""
                    {val aa = App.map(a)(otherThing); App.map(aa)(otherThing)}
                   """
    compareAndPrintIfDifferent(transformed, expected)
  }

  "AST generation with double extract" in {
    val ast = q"""
                import scalaz.IdiomBracket.auto.extract
                val a: Option[Option[String]] = ???
                def otherThing(a: String): String = ???
                val aa = otherThing(extract(extract(a)))
                otherThing(aa)
              """
    val transformed = transformLast(ast, nbLines = 2)
    val expected = q"""
                    val aa = App.map(a)(x1 => App.map(x1)(otherThing))
                    App.map(aa)(x2 => App.map(x2)(otherThing))
                   """
    compareAndPrintIfDifferent(transformed, expected, compareString = true)
  }

  "AST generation match with extract in lhs" in {
    val ast = q"""
                import scalaz.IdiomBracket.auto.extract
                val a: Option[String] = ???
                extract(a) match { case "hello" => "h" }
              """
    val transformed = transformLast(ast)
    val expected = q"""
                    App.map(a)(((x1) => x1 match {
                      case "hello" => "h"
                    }))
                   """
    compareAndPrintIfDifferent(transformed, expected, compareString = false)
  }

  "AST generation match with extract in lhs 2" in {
    val ast = q"""
                import scalaz.IdiomBracket.auto.extract
                val a: Option[String] = ???
                extract(a) match {
                  case "hello" => "h"
                  case _ => "e"
                }
              """
    val transformed = transformLast(ast)
    val expected = q"""
                    App.map(a)(((x1) => x1 match {
                      case "hello" => "h"
                      case _ => "e"
                    }))
                   """
    compareAndPrintIfDifferent(transformed, expected, compareString = false)
  }

  /*"AST generation match with unapply" in {
    val ast = q"""
                  import scalaz.IdiomBracket.auto.extract
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
                import scalaz.IdiomBracket.auto.extract
                val a: Option[String] = ???
                s"It's $${extract(a)}!"
              """
    val transformed = transformLast(ast)
    val expected = q"""
                       App.map(a)(((x1) => scala.StringContext.apply("It\'s ", "!").s(x1)))
                    """
    compareAndPrintIfDifferent(transformed, expected, compareString = true)
  }

  "AST generation match with stable identifier refering to extracted val" in {
    val ast = q"""
                import scalaz.IdiomBracket.auto.extract
                val a: Option[String] = ???
                val b: Option[String] = ???
                val bb = extract(b)
                extract(a) match {
                  case `bb` => "h"
                  case _ => "e"
                }
              """
    val transformed = transformLast(ast, nbLines = 2)
    val expected = q"""
                    val bb = b
                    App.apply2(a,bb)((x2,x1) => x2 match {
                      case `x1` => "h"
                      case _ => "e"
                    })
                   """
    compareAndPrintIfDifferent(transformed, expected)
  }

  /*"AST generation if statement" in {
    val ast = q"""
                import scalaz.IdiomBracket.auto.extract
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
                import scalaz.IdiomBracket.auto.extract
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

  "assumption future" in {
    import scala.concurrent.Future
    import scala.concurrent.Promise
    import scala.concurrent.ExecutionContext.Implicits.global
    import scala.concurrent.duration._

    val aPromise = Promise[Boolean]()
    val a = aPromise.future

    val bPromise = Promise[String]()
    val b = bPromise.future

    val cPromise = Promise[String]()
    val c = cPromise.future

    implicit val monad: Monad[Future] = scalaz.std.scalaFuture.futureInstance

    val f = Monad[Future].bind(a)(if(_) b else c)

    f.value == None

    aPromise.success(true)

    f.value == None

    bPromise.success("hello")

    Await.result(f, 1.second) == "hello"
  }

}

// vim: expandtab:ts=2:sw=2
