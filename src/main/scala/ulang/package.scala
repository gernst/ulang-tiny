package object ulang {
  import arse._

  type Env = Map[Var, Val]
  type Subst = Map[Var, Expr]

  object Env {
    def empty: Env = Map()
  }

  object Subst {
    def empty: Subst = Map()
  }

  object Eq extends Binary(Var("==", Infix(Non, 6))) {
    def zip(left: List[Expr], right: List[Expr]): List[Expr] = {
      if (left.length != right.length)
        sys.error("length mismatch: " + left + " " + right)
      zip(left zip right)
    }

    def zip(pairs: Iterable[(Expr, Expr)]): List[Expr] = {
      pairs map { case (a, b) => Eq(a, b) } toList
    }
  }

  object True extends Tag("True")
  object False extends Tag("False")

  object Zero extends Tag("0")
  object Succ extends Unary(Tag("+1", Postfix(11)))

  object Not extends Unary(Var("not", Prefix(5)))
  object And extends Binary(Var("/\\", Infix(Right, 4)))
  object Or extends Binary(Var("\\/", Infix(Right, 3)))
  object Imp extends Binary(Var("==>", Infix(Right, 2)))
  object Eqv extends Binary(Var("<=>", Infix(Non, 1)))

  def group[A, B](xs: List[(A, B)]) = {
    xs.groupBy(_._1).map {
      case (x, ys) => (x, ys.map(_._2))
    }
  }

  val sub = "₀₁₂₃₄₅₆₇₈₉"
  implicit class StringOps(self: String) {
    def prime = self + "'"

    def __(index: Int): String = {
      self + (index.toString map (n => sub(n - '0')))
    }

    def __(index: Option[Int]): String = index match {
      case None => self
      case Some(index) => this __ index
    }
  }

  implicit class SetOps[A](self: Set[A]) {
    def disjoint(that: Set[A]) = {
      (self & that).isEmpty
    }
  }
}