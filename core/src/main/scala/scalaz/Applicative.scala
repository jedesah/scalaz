package scalaz

////
/**
 * Applicative Functor, described in [[http://www.soi.city.ac.uk/~ross/papers/Applicative.html Applicative Programming with Effects]]
 *
 * Whereas a [[scalaz.Functor]] allows application of a pure function to a value in a context, an Applicative
 * also allows application of a function in a context to a value in a context (`ap`).
 *
 * It follows that a pure function can be applied to arguments in a context. (See `apply2`, `apply3`, ... )
 *
 * Applicative instances come in a few flavours:
 *  - All [[scalaz.Monad]]s are also `Applicative`
 *  - Any [[scalaz.Monoid]] can be treated as an Applicative (see [[scalaz.Monoid]]#applicative)
 *  - Zipping together corresponding elements of Naperian data structures (those of of a fixed, possibly infinite shape)
 *
 *  @see [[scalaz.Applicative.ApplicativeLaw]]
 */
////
trait Applicative[F[_]] extends Apply[F] { self =>
  ////
  def point[A](a: => A): F[A]

  // alias for point
  final def pure[A](a: => A): F[A] = point(a)

  // derived functions
  override def map[A, B](fa: F[A])(f: A => B): F[B] =
    ap(fa)(point(f))

  override def apply2[A, B, C](fa: => F[A], fb: => F[B])(f: (A, B) => C): F[C] =
    ap2(fa, fb)(point(f))

  // impls of sequence, traverse, etc

  def traverse[A, G[_], B](value: G[A])(f: A => F[B])(implicit G: Traverse[G]): F[G[B]] =
    G.traverse(value)(f)(this)

  def sequence[A, G[_]: Traverse](as: G[F[A]]): F[G[A]] =
    traverse(as)(a => a)

  import std.list._

  /** Performs the action `n` times, returning the list of results. */
  def replicateM[A](n: Int, fa: F[A]): F[List[A]] =
    listInstance.sequence(List.fill(n)(fa))(this)

  /** Performs the action `n` times, returning nothing. */
  def replicateM_[A](n: Int, fa: F[A]): F[Unit] =
    listInstance.sequence_(List.fill(n)(fa))(this)

  /** Filter `l` according to an applicative predicate. */
  def filterM[A](l: List[A])(f: A => F[Boolean]): F[List[A]] =
    l match {
      case Nil => point(List())
      case h :: t => ap(filterM(t)(f))(map(f(h))(b => t => if (b) h :: t else t))
    }

  /**
   * Returns the given argument if `cond` is `false`, otherwise, unit lifted into F.
   */
  def unlessM[A](cond: Boolean)(f: => F[A]): F[Unit] = if (cond) point(()) else void(f)
  
  /**
   * Returns the given argument if `cond` is `true`, otherwise, unit lifted into F.
   */
  def whenM[A](cond: Boolean)(f: => F[A]): F[Unit] = if (cond) void(f) else point(())
  
  /**The composition of Applicatives `F` and `G`, `[x]F[G[x]]`, is an Applicative */
  def compose[G[_]](implicit G0: Applicative[G]): Applicative[({type λ[α] = F[G[α]]})#λ] = new CompositionApplicative[F, G] {
    implicit def F = self

    implicit def G = G0
  }

  /**The product of Applicatives `F` and `G`, `[x](F[x], G[x]])`, is an Applicative */
  def product[G[_]](implicit G0: Applicative[G]): Applicative[({type λ[α] = (F[α], G[α])})#λ] = new ProductApplicative[F, G] {
    implicit def F = self

    implicit def G = G0
  }

  /** An `Applicative` for `F` in which effects happen in the opposite order. */
  def flip: Applicative[F] = new Applicative[F] {
    val F = Applicative.this
    def point[A](a: => A) = F.point(a)
    def ap[A,B](fa: => F[A])(f: => F[A => B]): F[B] =
      F.ap(f)(F.map(fa)(a => (f: A => B) => f(a)))
    override def flip = self
  }

  trait ApplicativeLaw extends ApplyLaw {
    /** `point(identity)` is a no-op. */
    def identityAp[A](fa: F[A])(implicit FA: Equal[F[A]]): Boolean =
      FA.equal(ap(fa)(point((a: A) => a)), fa)

    /** `point` distributes over function applications. */
    def homomorphism[A, B](ab: A => B, a: A)(implicit FB: Equal[F[B]]): Boolean =
      FB.equal(ap(point(a))(point(ab)), point(ab(a)))

    /** `point` is a left and right identity, F-wise. */
    def interchange[A, B](f: F[A => B], a: A)(implicit FB: Equal[F[B]]): Boolean =
      FB.equal(ap(point(a))(f), ap(f)(point((f: A => B) => f(a))))

    /** `map` is like the one derived from `point` and `ap`. */
    def mapLikeDerived[A, B](f: A => B, fa: F[A])(implicit FB: Equal[F[B]]): Boolean =
      FB.equal(map(fa)(f), ap(fa)(point(f)))
  }
  def applicativeLaw = new ApplicativeLaw {}

  ////
  val applicativeSyntax = new scalaz.syntax.ApplicativeSyntax[F] { def F = Applicative.this }
}

import language.experimental.macros
import scala.annotation.compileTimeOnly
import scala.concurrent.Future
import scala.reflect.runtime.universe._

object Applicative {
  @inline def apply[F[_]](implicit F: Applicative[F]): Applicative[F] = F

  ////

  implicit def monoidApplicative[M:Monoid]: Applicative[({type λ[α] = M})#λ] = Monoid[M].applicative

  ////
}

object IdiomBracket {
  def apply[T](x: T): Option[T] = macro idiomBracket[T]

  @compileTimeOnly("`extract` must be enclosed in an `IdiomBracket`")
  def extract[T](option: Option[T]): T = ??? // Should be removed by macro expansion

  def debug(x: Any): Unit = macro debugImpl

  object auto {
    @compileTimeOnly("`extract` must be enclosed in an `IdiomBracket`")
    implicit def extract[T](option: Option[T]): T = ??? // Should be removed by macro expansion
  }

  import scala.reflect.macros.blackbox.Context

  def debugImpl(c: Context)(x: c.Expr[Any]): c.Expr[Unit] = {
    import c.universe._
    println(show(x.tree))
    println(showRaw(x.tree))
    val message = Literal(Constant(show(x.tree) + ": "))
    val result = q"""println($message + (${x.tree}))"""
    c.Expr[Unit](result)
  }

  def idiomBracket[T: c.WeakTypeTag](c: Context)(x: c.Expr[T]): c.Expr[Option[T]] = {
    val result = transformAST(c.universe)(x.tree)
    c.Expr[Option[T]](result)
  }

  def transformAST(u: scala.reflect.api.Universe)(tree: u.Tree): u.Tree = {
    import u._
    def transformR(tree: u.Tree): u.Tree = tree match {
        case Apply(ref, args) =>
          if (!extractsArePresent(ref)) {
              val cleanedArgs = cleanArgs(args)
              val applyTerm = getApplyTerm(cleanedArgs.length)
              q"Applicative[Option].$applyTerm(..$cleanedArgs)($ref)"
          }
          else {
            val Select(exprRef, methodName) = ref
            val argsAfterRewrite = exprRef :: args
            val cleanedArgs = cleanArgs(argsAfterRewrite)
            val applyTerm = getApplyTerm(argsAfterRewrite.length)
            val methodNameTerm = methodName.toTermName
            q"Applicative[Option].$applyTerm(..$cleanedArgs)(_.$methodNameTerm(_,_))"
          }
        case Block(exprs, finalExpr) => {
          val newExprs = (exprs :+ finalExpr).foldLeft[(List[String], List[u.Tree])]((Nil, Nil)) { (accu, expr) =>
            val (names, exprs) = accu
            expr match {
              // We need to remember the name of the value definition so that we can add extract methods later so that the right thing happens
              case ValDef(mods, name, tpt, rhs) => (name.toString :: names, exprs :+ ValDef(mods, name, TypeTree(), transformR(addExtract(rhs, names))))
              // If it's just an identifier, let's leave it as is.
              case ident: Ident => (names, exprs :+ Ident(TermName(ident.name.toString)))
              // Anything else, we need to add extracts to identifiers of transformed `ValDef`s because we lifted the type of the symbol they refer to.
              case _ => (names, exprs :+ transformR(addExtract(expr, names)))
            }
          }._2
          Block(newExprs.init, newExprs.last)
        }
        case _ => tree
    }

    def getApplyTerm(arity: Int) = {
      assert(arity <= 12, "scalaz does not define an apply13 or more which is necessary of our rewrite to work. Reformat your code to avoid functions receiving more than 12 parameters.")
      val applyFunName = if (arity == 1) "map"
      else s"apply$arity"
      TermName(applyFunName)
    }

    def addExtract(expr: u.Tree, names: List[String]): u.Tree = {
      object AddExtract extends Transformer {
        override def transform(tree: u.Tree): u.Tree = tree match {
          case ident@Ident(name) => {
            val untypedIdent = Ident(TermName(name.toString))
            if (names.contains(name.toString)) q"scalaz.IdiomBracket.extract($untypedIdent)" else ident
          }
          case _ => super.transform(tree)
        }
      }
      AddExtract.transform(expr)
    }

    def extractsArePresent(expr: u.Tree): Boolean = {
      var result = false
      object FindExtract extends Traverser {
        override def traverse(tree: u.Tree): Unit =
          if(isExtractFunction(tree)) result = true
          else super.traverse(tree)
      }
      FindExtract.traverse(expr)
      result
    }

    def isExtractFunction(tree: u.Tree): Boolean = {
      val extractMethodNames = List("scalaz.IdiomBracket.extract", "scalaz.IdiomBracket.auto.extract")
      tree match {
        case extract: Apply if extractMethodNames.contains(extract.symbol.fullName) => true
        case extract: Apply if extract.symbol == NoSymbol => true
        case _ => false
      }
    }

    def cleanArgs(args: List[u.Tree]) = args.map {
        case extract if isExtractFunction(extract) => extract.asInstanceOf[Apply].args(0)
        case normalArg => {
          val newArg = transformR(normalArg)
          // If the argument has not undergone a transformation, then lift the computation in order
          // to fit into the new AST
          if (newArg equalsStructure normalArg) q"Some($normalArg)"
          // If it has been transformed than it has already been lifter in sort
          // because of the transformation required to remove the extract
          else newArg
        }
      }

    tree match {
      case Apply(_,_) => transformR(tree)
      case Block(_) => transformR(tree)
      case _ => throw new UnsupportedOperationException("Needs to be a simple expression or a block statement")
    }
  }
}
