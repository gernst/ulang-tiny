package ulang

import arse._
import arse.implicits._

class Parse(context: Context) {
  import context._

  val eq_prec = Eq.op.fixity.prec

  implicit object whitespace
    extends Whitespace("(\\s|(//.*\\n))*")

  def parens[A](p: Parser[A]) = "(" ~ p ~ ")"
  def bracks[A](p: Parser[A]) = "[" ~ p ~ "]"

  val keywords = Set(
    "define", "data", "notation", "eval", "assume", "show", "proof", "inductive", "coinductive",
    ",", ";", "(", ")", "{", "}", "[", "]", "->", "|", "_",
    "if", "then", "else",
    "let", "in", "match", "with",
    "lambda", "exists", "forall")

  val s = S("""[^ \r\n\t\f()\[\],;:\'\"]+""")
  val c = L("::", ":", "[]")
  val n = s | c
  val name = P(n filterNot keywords)

  object Id extends (String => Id) {
    def apply(name: String): Id = {
      val fixity = if (mixfix contains name) mixfix(name) else Nilfix
      if ((data contains name) || (name.head.isUpper)) Tag(name, fixity) else Var(name, fixity)
    }
  }

  object unapps extends ((String, List[Pat]) => Pat) {
    def apply(fun: String, args: List[Pat]) = {
      UnApps(Id(fun), args)
    }
  }

  object apps extends ((String, List[Expr]) => Expr) {
    def apply(fun: String, args: List[Expr]) = {
      Apps(Id(fun), args)
    }
  }

  def id = P(Id(name))
  def x = id collect { case x: Var => x }

  val id_nonmixfix = id filterNot isMixfix

  val pat: Mixfix[String, Pat] = M(unapp, name, unapps, context)
  val pat_arg: Parser[Pat] = P(parens(pat_open) | wildcard | strict | id_nonmixfix)
  val pat_open = pat | id

  val expr: Mixfix[String, Expr] = M(app, name, apps, context)
  val expr_arg: Parser[Expr] = P(parens(expr_open) | ite | let | lam | ex | all | mtch | id_nonmixfix)
  val expr_open = expr | id

  val wildcard = Wildcard("_")
  val unapp = UnApps(pat_arg ~ pat_arg.*)
  val strict = Strict("!" ~ pat_arg)

  val app = Apps(expr_arg ~ expr_arg.*)
  val ite = Ite("if" ~ expr ~ "then" ~ expr ~ "else" ~ expr)

  val eq = Case1(pat_arg ~ "=" ~ expr)
  val eqs = eq ~+ ","
  val let = Let("let" ~ eqs ~ "in" ~ expr)

  val cs = Case(pat_arg.+ ~ "->" ~ expr)
  val css = cs ~+ "|"
  val lam = Lam("lambda " ~ css)
  // val bind = Binder(id_bind ~ cs)

  val quant = x.+ ~ "->" ~ expr
  val ex = Ex("exists" ~ quant)
  val all = All("forall" ~ quant)

  val mtch = Match("match" ~ expr_arg.+ ~ "with" ~ css)

  val tactic: Parser[Tactic] = P(ind | coind | split | have)
  val ind = Ind("induction" ~ pat ~ ret(Least))
  val coind = Ind("induction" ~ pat ~ ret(Greatest))
  val split = Split("cases" ~ pat)
  val have = Have("have" ~ expr)

  val pat_high = pat above (eq_prec + 1)
  val attr = L("rewrite")
  val attrs = bracks(attr.*) | ret(Nil)
  val df = Def(pat_high ~ "==" ~ expr ~ attrs)

  def section[A](keyword: String, p: Parser[A]): Parser[List[A]] = {
    keyword ~ (p ~ ";").*
  }

  val assoc = Left("infixl") | Right("infixr") | Non("infix")
  val prefix = Prefix("prefix" ~ int)
  val postfix = Postfix("postfix" ~ int)
  val infix = Infix(assoc ~ int)

  val fixity: Parser[Fixity] = prefix | postfix | infix
  def fix = name.+ ~ bracks(fixity)

  val assume = section("assume", expr)
  val show = "show" ~ expr ~ ";"

  def data_declare = name.+ map {
    names =>
      data ++= names
      names
  }

  val notation_declare = fix map {
    case (names, fixity) =>
      context declare (names, fixity)
      (names, fixity)
  }

  val cmd: Parser[Cmd] = P(defs | evals | datas | notation | thm | least | greatest)

  val defs = Defs(section("define", df))
  val evals = Evals(section("eval", expr))
  val datas = Datas(section("data", data_declare) map (_.flatten))
  val notation = Notation(section("notation", notation_declare))
  val least = Fix(section("inductive", expr) ~ ret(Least))
  val greatest = Fix(section("coinductive", expr) ~ ret(Greatest))

  val proof = "proof" ~ tactic ~ ";"
  val thm = Thm(assume ~ show ~ proof.?) | Thm0(show ~ proof.?)

  val script = cmd.*
}