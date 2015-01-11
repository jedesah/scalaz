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
import scala.collection.mutable.ListBuffer

object Applicative {
  @inline def apply[F[_]](implicit F: Applicative[F]): Applicative[F] = F

  ////

  implicit def monoidApplicative[M:Monoid]: Applicative[({type λ[α] = M})#λ] = Monoid[M].applicative

  ////
}

object IdiomBracket {
  def apply[F[_]: Applicative,T](x: T): F[T] = macro idiomBracket[T,F]
  def apply2[T](x: T): Option[Option[T]] = macro idiomBracket2[T]
  def monad[F[_]: Monad,T](x: T): F[T] = macro idiomBracketMonad[T,F]

  def control(x: String): Option[String] = macro controlImpl

  @compileTimeOnly("`extract` must be enclosed in an `IdiomBracket`")
  def extract[F[_], T](applicative: F[T]): T = ??? // Should be removed by macro expansion

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

  def idiomBracket[T: c.WeakTypeTag, F[_]](c: Context)(x: c.Expr[T])(ap: c.Expr[Applicative[F]]): c.Expr[F[T]] = {
    import c.universe._
    val applicativeInstance = ap.tree
    val result = transformAST(c.universe, () => c.freshName())(x.tree, applicativeInstance, monadic = false)
    if (!result.isDefined) c.warning(c.enclosingPosition, "IdiomBracket merely lifted expression, there is a probably a better more explicit way of achieving the same result")
    c.Expr[F[T]](result.getOrElse(q"$applicativeInstance.pure(${x.tree})"))
  }

  def idiomBracketMonad[T, F[_]](c: Context)(x: c.Expr[T])(m: c.Expr[Monad[F]]): c.Expr[F[T]] = {
    import c.universe._
    val monadInstance = m.tree
    val result = transformAST(c.universe, () => c.freshName())(x.tree, monadInstance, monadic = true)
    if (!result.isDefined) c.warning(c.enclosingPosition, "IdiomBracket merely lifted expression, there is a probably a better more explicit way of achieving the same result")
    c.Expr[F[T]](result.getOrElse(q"$monadInstance.pure(${x.tree})"))
  }

  def controlImpl(c: Context)(x: c.Expr[String]): c.Expr[Option[String]] = {
    import c.universe._
    val result = x.tree match {
      case Match(expr, cases) =>
        println(cases)
        //val matchz = Match(q"""List("hello")""", cases.map(c.untypecheck(_).asInstanceOf[CaseDef]))
        val matchz = Match(q"""List("hello")""", cases.map{case cq"$x1 => $x2" => cq"$x1 => $x2"})
        q"Some($matchz)"
        q"""Some(List("5")).map{a => a;$matchz}"""
      case a => q"Some($a)"
    }
    c.Expr[Option[String]](c.untypecheck(result))
  }

  def idiomBracket2[T: c.WeakTypeTag](c: Context)(x: c.Expr[T]): c.Expr[Option[Option[T]]] = {
    import c.universe._
    val result = transformAST(c.universe, () => c.freshName())(x.tree, q"scalaz.Applicative[Option]", monadic = false)
    if (!result.isDefined) c.warning(c.enclosingPosition, "IdiomBracket merely lifted expression, there is a probably a better more explicit way of achieving the same result")
    c.Expr[Option[Option[T]]](result.getOrElse(q"Some(Some($x.tree))"))
  }

  /**
    *
    * @param u The universe of the Trees. Required to operate under current Scala reflection architecture. Trees cannot
    *          exist without a universe.
    * @param freshName Function that generates fresh names for use in the AST transformation
    * @param tree Tree to transform
    * @return Some(Tree) if the tree was transformed or none if it was not transformed
    */
  def transformAST(u: scala.reflect.api.Universe, freshName: () => String)(tree: u.Tree, applicativeInstance: u.Tree, monadic: Boolean): Option[u.Tree] = {
    import u._
    def transformR(tree: u.Tree): (u.Tree, Int) = tree match {
      case fun: Apply if isExtractFunction(fun) => (fun.args(0), 1)
      case Apply(ref, args) =>
        val (ref1, args1) = if (!extractsArePresent(ref)) {
          ref match {
            case Select(exprRef, methodName) => (createMethodWithLHS(methodName, exprRef, args.size, freshName), args)
            case _ => (ref, args)
          }
        } else {
          val Select(exprRef, methodName) = ref
          (createMethod(methodName, args.size, freshName), exprRef :: args)
        }
        val liftedArgs = args1.map(lift(_))
        val applyTerm = getApplyTerm(liftedArgs.length)
        if (liftedArgs.forall(!isExtractFunction(_))) (q"$applicativeInstance.$applyTerm(..$liftedArgs)($ref1)", 1)
        else {
          val names: List[u.TermName] = List.fill(liftedArgs.size)(freshName()).map(TermName(_))
          val transformedArgs = liftedArgs.zip(names).map { case (arg, name) =>
            val ident = Ident(name)
            if (extractsArePresent(arg)) ident
            else q"$applicativeInstance.pure($ident)"
          }
          val inner = createFunction(q"$applicativeInstance.$applyTerm(..$transformedArgs)($ref1)", names)
          val reLiftedArgs = liftedArgs.map(lift(_))
          (q"$applicativeInstance.$applyTerm(..$reLiftedArgs)($inner)", 2)
        }
      case Block(exprs, finalExpr) => {
        var arityLastTransform: Int = 0
        val newExprs = (exprs :+ finalExpr).foldLeft[(Map[String, Int], List[u.Tree])]((Map(), Nil)) { (accu, expr) =>
          val (names, exprs) = accu
          expr match {
            // We need to remember the name of the value definition so that we can add extract methods later so that the right thing happens
            case ValDef(mods, name, tpt, rhs) =>
              val (tRHS, transformArity) = transformR(addExtractR(rhs, names))
              arityLastTransform = transformArity
              (names + (name.toString -> transformArity), exprs :+ ValDef(mods, name, TypeTree(), tRHS))
            // If it's just an identifier, let's leave it as is but reconstruct it so that it looses it's type.
            case ident: Ident =>
              arityLastTransform = names(ident.name.toString)
              (names, exprs :+ Ident(TermName(ident.name.toString)))
            // Anything else, we need to add extracts to identifiers of transformed `ValDef`s because we lifted the type of the symbol they refer to.
            case _ =>
              val (transformed, transformArity) = transformR(addExtractR(expr, names))
              arityLastTransform = transformArity
              (names, exprs :+ transformed)
          }
        }._2
        (Block(newExprs.init, newExprs.last), arityLastTransform)
      }
      // TODO: Figure out why unchanged case pattern seems to go bonky in macro
      case Match(expr, cases) =>
        val (tCases, argsWithWhatTheyReplace: List[List[(u.TermName, u.Tree)]]@unchecked) = cases.map { case cq"$x1 => $x2" =>
          val (newX1, argsWithWhatTheyReplace1) =
            if (extractsArePresent(x1)) replaceExtractWithRef(x1)
            else (x1, (Nil))
          val (newX2, argsWithWhatTheyReplace2) =
            if (extractsArePresent(x2)) {
              val paramName = TermName(freshName())
              (Ident(paramName), (List(paramName,x2)))
            }
            else (x2, (Nil))
          (cq"$newX1 => $newX2", argsWithWhatTheyReplace1 ++ argsWithWhatTheyReplace2)
        }.unzip
        val (names, args) = argsWithWhatTheyReplace.flatten.unzip
        val allArgs = (expr :: args).map(lift(_))
        val applyTerm = getApplyTerm(allArgs.size)
        val lhsName = TermName(freshName())
        val function = createFunction(q"$lhsName match { case ..$tCases}", lhsName :: names)
        (q"$applicativeInstance.$applyTerm(..$allArgs)($function)", 1)
      case If(expr, trueCase, falseCase) =>
        if (!monadic) {
          val liftedParts = List(expr, trueCase, falseCase).map(lift(_))
          (q"$applicativeInstance.apply3(..$liftedParts)(if(_) _ else _)", 1)
        }
        else {
          val List(exprT, trueCaseT, falseCaseT) = List(expr, trueCase, falseCase).map(lift(_))
          (q"$applicativeInstance.bind($exprT)(if(_) $trueCaseT else $falseCaseT)", 1)
        }
      case _ => (tree, 0)
    }

    def getApplyTerm(arity: Int) = {
      assert(arity <= 12, "scalaz does not define an apply13 or more which is necessary of our rewrite to work. Reformat your code to avoid functions receiving more than 12 parameters.")
      val applyFunName = if (arity == 1) "map"
      else s"apply$arity"
      TermName(applyFunName)
    }

    def createFunction(rhs: u.Tree, args: List[u.TermName]) = {
      val lhs = args.map( name => ValDef(Modifiers(Flag.PARAM), name, TypeTree(), EmptyTree))
      Function(lhs, rhs)
    }

    def createMethod(methodName: u.Name, nArgs: Int, freshName: () => String) = {
      val names = List.fill(nArgs + 1)(freshName())
      val lhs = names.map( name => ValDef(Modifiers(Flag.PARAM | Flag.SYNTHETIC), TermName(name), TypeTree(), EmptyTree))
      val args = names.map(name => Ident(TermName(name)))
      val rhs = Apply(Select(args.head, methodName), args.tail)
      Function(lhs, rhs)
    }

    def createMethodWithLHS(methodName: u.Name, select: u.Tree, nArgs: Int, freshName: () => String) = {
      val names = List.fill(nArgs)(freshName())
      val lhs = names.map( name => ValDef(Modifiers(Flag.PARAM | Flag.SYNTHETIC), TermName(name), TypeTree(), EmptyTree))
      val args = names.map(name => Ident(TermName(name)))
      val rhs = Apply(Select(select, methodName), args)
      Function(lhs, rhs)
    }

    def replaceExtractWithRef(pattern: u.Tree): (u.Tree, (List[(u.TermName,u.Tree)])) = {
      val namesWithReplaced = ListBuffer[(u.TermName, u.Tree)]()
      object ReplaceExtract extends Transformer {
        override def transform(tree: u.Tree): u.Tree = tree match {
          case fun: Apply if isExtractFunction(fun) =>
            val name = TermName(freshName())
            namesWithReplaced += ((name, fun))
            q"`$name`"
          case _ => super.transform(tree)
        }
      }
      val result = ReplaceExtract.transform(pattern)
      (result, namesWithReplaced.toList)
    }

    def addExtractR(expr: u.Tree, names: Map[String, Int]): u.Tree = {
      object AddExtract extends Transformer {
        override def transform(tree: u.Tree): u.Tree = tree match {
          case ident@Ident(name) => {
            val untypedIdent = Ident(TermName(name.toString))
            if (names.keys.toList.contains(name.toString))
              (0 until names(name.toString)).foldLeft[u.Tree](untypedIdent)((tree, _) => addExtract(tree))
            else ident
          }
          case _ => super.transform(tree)
        }
      }
      AddExtract.transform(expr)
    }

    def addExtract(expr: u.Tree): u.Tree = {
      q"scalaz.IdiomBracket.extract($expr)"
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
        case extract if extract.symbol != null && extractMethodNames.contains(extract.symbol.fullName) => true
        case q"scalaz.IdiomBracket.extract($_)" => true
        case _ => false
      }
    }

    /**
     * Lifts the following expression to an Applicative either by removing an extract function (it can be deeply nested)
     * or by simply adding a call to the pure function of the applicativeInstance if the expression contained no extract
     * functions.
     * @param expr Expression to be lifted
     * @return New expression that has been lifted
     */
    def lift(expr: u.Tree): u.Tree = expr match {
      case extract: Apply if isExtractFunction(extract) => extract.args(0)
      case normal => {
        val (newArg, transformArity) = transformR(normal)
        // If the argument has not undergone a transformation, then lift the computation in order
        // to fit into the new AST
        if (transformArity == 0) q"$applicativeInstance.pure($normal)"
        // If it has been transformed than it has already been lifter in sort
        // because of the transformation required to remove the extract
        else newArg
      }
    }

    val (result, transformArity) = transformR(tree)
    if (transformArity == 0) None else Some(result)
  }
}
