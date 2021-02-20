package ulang

import arse._

sealed trait Expr extends Expr.term with Pretty {
  def free: Set[Id]

  def <=(that: Expr): Boolean = (this, that) match {
    case (_, Wildcard) =>
      true
    case (App(fun1,arg1), App(fun2, arg2)) =>
      fun1 <= fun2 && arg1 <= arg2
    case _ =>
      this == that
  }

  /** Check if this expression represents a formula */
  def isFormula: Boolean = this match {
    case True => true
    case False => true
    case Zero => false
    // technically we could have a let statement that returns a formula
    case Let(_, _) => false
    case Match(_, _) => false
    // technically we could have a lamda expression that returns a formula
    // when applied correctly
    case Lam(_) => false
    case Bind(_, _, body) => body.isFormula
    case Not(e) => e.isFormula
    case Or(e1, e2) => e1.isFormula && e2.isFormula
    case And(e1, e2) => e1.isFormula && e2.isFormula
    case Imp(e1, e2) => e1.isFormula && e2.isFormula
    case Eqv(e1, e2) => e1.isFormula && e2.isFormula
    case App(fun, arg) => fun.isPredicate && !arg.isFormula
  }

  /** Check if this expression is a predicate name */
  def isPredicate: Boolean = this match {
    case Id(_, _) => true
    case _ => false
  }

  def isProofTerm: Boolean = this match{
    case Pair(e1, e2) =>
      (e1.isProofTerm && e2.isProofTerm) || // proof term for AND
      (e2.isProofTerm) // FIXME e1 should be the witness for an ∃ proof
    case LeftE(e) => e isProofTerm
    case RightE(e) => e isProofTerm
    case Lam(cases) => cases.forall(_.body.isProofTerm) // FIXME this is not really correct
    case _ => false
  }

}

object ProofTermChecker {

  /**
   * A pattern matching abbreviation for lambda expressions with just one
   * pattern and one argument.
   */
  object Lam1 {
    def unapply(e: Expr) = e match {
      case Lam(List(Case(List(id@Id(_, _)), body))) => Some((id, body))
      case _ => None
    }
  }

  /** Check a proof
   *
   *  The proof is assumed to have no global assumtions.
   */
  def check(proof: Expr, goal: Expr): Boolean = check(Map(), proof, goal)

  /** Check a proof with context
   *
   *  This implements checking of proofs according to the
   *  Brouwer-Heyting-Kolmogorov interpretation of proofs (see Schwichtenberg
   *  & Wainer "Proofs and Computations", 2012, CUP, p313-314).
   *
   *  If a proof should be allowed to use axioms, they need to be present in
   *  the context.
   *
   *  TODO use a rich return type like `type Error = Option[String]`
   */
  def check(assumptions: Map[Id, Expr], proof: Expr, goal: Expr): Boolean =
    (proof, goal) match {

      // Proof by assumption has to be the first case, this makes it possible
      // to match against any goal (even "False").  If the given goal is not
      // in the context we fall through to the other cases.
      case (id: Id, _) if assumptions.contains(id) =>
        assumptions(id) == goal
      // TODO if the id was not found in the local assumptions we want to look
      // at the gloablly available lemmas  (and axioms etc) or at defined
      // functions which the user might use to proof something.
      // Here local assumptions shadow lemmas which in turn shadow global
      // functions.
      //case (id: Id, _) if global_lemmas.contains(id) =>
      //  canBeUnified(global_lemmas(id), goal)
      //case (id: Id, _) if funs.contains(id) =>
      //  canBeUnified(funs(id), goal)

      // special cases
      case (True, True) => true // we use "True" to represent a trivial proof

      // propositional logic: introduction rules
      case (Pair(p1, p2), And(f1, f2)) => check(assumptions, p1, f1) &&
                                          check(assumptions, p2, f2)
      case (LeftE(p), Or(f, _)) => check(assumptions, p, f)
      case (RightE(p), Or(_, f)) => check(assumptions, p, f)
      // special case for one argument lambdas with a variable pattern
      case (Lam1(id, body), Imp(f1, f2)) =>
        check(assumptions + (id -> f1), body, f2)
      // and elimination
      case (Lam(List(Case(List(Pair(p1: Id, p2: Id)), body))), Imp(And(f1, f2), f3)) =>
        check(assumptions + (p1 -> f1) + (p2 -> f2), body, f3)
      case (Lam(List(Case(List(LeftE(p1: Id)), body))), Imp(Or(f1, _), f2)) =>
        check(assumptions + (p1 -> f1), body, f2)
      case (Lam(List(Case(List(RightE(p1: Id)), body))), Imp(Or(_, f1), f2)) =>
        check(assumptions + (p1 -> f1), body, f2)

      // Special cases for modus ponens
      // this is only a simpler case of the next case, the implementation
      // there also checks this case correctly
      case (App(f: Id, arg: Id), _)
        if assumptions.contains(f) && assumptions.contains(arg)
        => assumptions(f) == Imp(assumptions(arg), goal)
      case (App(f: Id, arg), _)
        if assumptions.contains(f) && (assumptions(f) match {
          case Imp(precond, `goal`) => check(assumptions, arg, precond)
          case _ => false
        })
        => true
      case (App(Lam1(id, body), arg), _) =>
        check(assumptions, body.subst(Map(id -> arg)), goal)

      // propositional logic: elimination rules TODO
      //case (App(f, args), _) if functionArgumentsMatch(f, args) && bodyTypeMatches()

      // predicate logic
      case (Pair(w: Id, p), Bind(Ex, List(v), body)) =>  // only for one variable
        check(assumptions, p, body.rename(Map(v -> w)))
      case (Lam1(id, body1), Bind(All, List(v), body2)) =>  // only for one variable
        // FIXME do I need to generate a new name instead of id?  If I use id
        // itself do I need to rename on body1 then?  I think no & no.
        check(assumptions, body1.rename(Map(id -> id)), body2.rename(Map(v -> id)))

      // TODO everything else needs to be evaluated and then checked again
      // False is implicit here
      //case _ => false
    }

  // TODO these functions are suggested by Gidon in order to check elimination
  // and introduction rules seperately.
  def bind(ctx: Map[Id, Expr], pat: Expr, assm: Expr): Map[Id,Expr] =
    (pat, assm) match {
      case (And(p1,p2), And(a1,a2)) => bind(bind(ctx, p1, a1), p2, a2)
    }
  def elim(ctx: Map[Id, Expr], pats: List[Expr], body: Expr, goal: Expr): Boolean =
    (pats, goal) match {
      case (Nil, _) => check(ctx, body, goal)
      case (pat::rest, Imp(assm, concl)) =>
        val ctx_ = bind(ctx, pat, assm)
        elim(ctx_, rest, body, concl)
    }
  def elim(ctx: Map[Id, Expr], cs: Case, goal: Expr): Boolean = ???
  def elim(ctx: Map[Id, Expr], cases: List[Case], goal: Expr): Boolean =
    cases.forall(elim(ctx, _, goal))
}

object Expr extends Alpha[Expr, Id]

sealed trait Val extends Pretty
sealed trait Norm extends Val
sealed trait Data extends Norm

case object Wildcard extends Expr {
  def free = Set()
  def rename(re: Map[Id, Id]) = this
  def subst(su: Map[Id, Expr]) = this
}

case class Id(name: String, index: Option[Int]) extends Expr with Data with Expr.x {
  import context._
  def this(name: String) = this(name, None)
  def free = if(isTag(this) || isFun(this)) Set() else Set(this)
  def fresh(index: Int) = Id(name, Some(index))
}

object Id extends (String => Id) {
  def apply(name: String): Id = {
    Id(name, None)
  }
}

case class App(fun: Expr, arg: Expr) extends Expr {
  def free = fun.free ++ arg.free
  def rename(re: Map[Id, Id]) = App(fun rename re, arg rename re)
  def subst(su: Map[Id, Expr]) = App(fun subst su, arg subst su)
}

case class Ite(test: Expr, left: Expr, right: Expr) extends Expr {
  def free = test.free ++ left.free ++ right.free
  def rename(re: Map[Id, Id]) = Ite(test rename re, left rename re, right rename re)
  def subst(su: Map[Id, Expr]) = Ite(test subst su, left subst su, right subst su)
}

case class Case(pats: List[Expr], body: Expr) extends Expr.bind[Case] with Pretty {
  def arity = pats.length
  def free = body.free -- bound
  def bound = pats.free
  def rename(a: Map[Id, Id], re: Map[Id, Id]) = Case(pats rename a, body rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) = Case(pats rename a, body subst su)
}

case class Case1(pat: Expr, arg: Expr) extends Pretty {
  def free = arg.free
  def bound = pat.free
  def rename(a: Map[Id, Id], re: Map[Id, Id]) = Case1(pat rename a, arg rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) = Case1(pat rename a, arg subst su)
}

case class Lam(cases: List[Case]) extends Expr {
  def free = cases.free
  def bound = cases.bound
  def rename(re: Map[Id, Id]) = Lam(cases rename re)
  def subst(su: Map[Id, Expr]) = Lam(cases subst su)
}

case class Match(args: List[Expr], cases: List[Case]) extends Expr {
  def free = args.free ++ cases.free
  def rename(re: Map[Id, Id]) = Match(args rename re, cases rename re)
  def subst(su: Map[Id, Expr]) = Match(args subst su, cases subst su)
}

case class Let(eqs: List[Case1], body: Expr) extends Expr with Expr.bind[Let] {
  def pats = eqs.pats
  def args = eqs.args
  def bound = eqs.bound
  def free = eqs.free ++ (body.free -- bound)
  def rename(a: Map[Id, Id], re: Map[Id, Id]) = Let(eqs rename (a, re), body rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) = Let(eqs subst (a, su), body subst su)
}

sealed trait Quant extends ((List[Id], Expr) => Expr) {
  def apply(args: List[Id], body: Expr) = args match {
    case Nil => body
    case _ => Bind(this, args, body)
  }

  def unapply(expr: Expr) = expr match {
    case Bind(quant, args, body) if quant == this =>
      Some((args, body))
    case _ =>
      None
  }
}

case object Ex extends Quant
case object All extends Quant

case class Bind(quant: Quant, args: List[Id], body: Expr) extends Expr with Expr.bind[Bind] {
  def bound = args.toSet
  def free = body.free -- bound
  def rename(a: Map[Id, Id], re: Map[Id, Id]) = Bind(quant, args rename a, body rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) = Bind(quant, args rename a, body subst su)
}

case class Obj(fun: Data, arg: Val) extends Data

case class Curry(cases: List[Case], rargs: List[Val], lex: Env) extends Data {
  assert(cases.nonEmpty)
  assert(cases forall (_.arity == arity))
  assert(rargs.length <= arity)
  def isComplete = arity == rargs.length
  def arity = cases.head.arity
}

case class Defer(expr: Expr, lex: Env) extends Val {
  override def toString = expr.toString
  lazy val norm = Eval.norm(expr, lex)
}
