package ulang

sealed trait Tactic extends Pretty
case object Auto extends Tactic
case class Ind(pat: Pat, kind: FixKind) extends Tactic
case class Split(pat: Pat) extends Tactic
case class Have(expr: Expr) extends Tactic

sealed trait Pos { def unary_!(): Pos }
case object Ant extends Pos { def unary_! = Suc }
case object Suc extends Pos { def unary_! = Ant }

case class Intro(pre: List[Expr], post: Expr) {
  def pat = post.toPat
  def free = pre.free ++ post.free
  def rename(re: Map[Var, Var]) = Intro(pre rename re, post rename re)
  def subst(su: Map[Var, Expr]) = Intro(pre subst su, post subst su)
}

sealed trait Proof {
  def isClosed: Boolean
}

sealed trait Goal extends Proof {
  def assume(phi: Expr): Goal
  def assert(phi: Expr): Goal

  def assume(args: List[Expr]): Goal = {
    args.foldLeft(this)(_ assume _)
  }

  def assert(args: List[Expr]): Goal = {
    args.foldLeft(this)(_ assert _)
  }
}

case object Closed extends Goal {
  def isClosed = true
  def assume(phi: Expr) = this
  def assert(phi: Expr) = this
}

case class Step(prems: List[Proof], concl: Open, tactic: Tactic) extends Proof {
  def isClosed = prems forall (_.isClosed)
}

case class Open(eqs: Subst, rant: List[Expr], rsuc: List[Expr]) extends Goal with Pretty {
  def pre = Eq.zip(eqs) ::: ant
  def ant = rant.reverse
  def suc = rsuc.reverse
  def free = rant.free ++ rsuc.free

  def isClosed = false

  import Prove._

  def contains(phi: Expr) = {
    (rant contains phi) || (rsuc contains not(phi))
  }

  def assume(phi: Expr): Goal = phi match {
    case True => this
    case False => Closed
    case _ if this contains not(phi) => Closed
    case Not(phi) => this assert phi
    case And(phi, psi) => this assume phi assume psi
    case Eq(x: Var, e) if !(e.free contains x) => copy(eqs = eqs + (x -> e))
    case Eq(e, x: Var) if !(e.free contains x) => copy(eqs = eqs + (x -> e))
    case _ => copy(rant = phi :: rant)
  }

  def assert(phi: Expr): Goal = phi match {
    case False => this
    case True => Closed
    case _ if this contains phi => Closed
    case Not(phi) => this assume phi
    case Imp(phi, psi) => this assume phi assert psi
    case Or(phi, psi) => this assert phi assert psi
    case _ => copy(rsuc = phi :: rsuc)
  }
}

object Goal {
  val empty = Open(Subst.empty, Nil, Nil)
}