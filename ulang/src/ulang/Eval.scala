package ulang

import arse.backtrack
import arse.Control

object Eval {
  import context._

  def equal(v1: Val, v2: Val): Boolean = {
    const(v1) == const(v2)
  }

  def bind(pat: Expr, arg: Val, env: Env): Env = pat match {
    case Wildcard =>
      env
    case id: Id if isTag(id) =>
      if (id == force(arg)) env
      else backtrack
    case id: Id if env contains id =>
      if (equal(env(id), arg)) env
      else backtrack
    case id: Id =>
      env + (id -> arg)
    case App(pat1, pat2) =>
      force(arg) match {
        case Obj(arg1, arg2) => bind(pat2, arg2, bind(pat1, arg1, env))
        case _ => backtrack
      }
    case _ =>
      backtrack
  }

  def bind(pats: List[Expr], args: List[Val], env: Env): Env = (pats, args) match {
    case (Nil, Nil) => env
    case (pat :: pats, arg :: args) => bind(pats, args, bind(pat, arg, env))
    case _ => fail("argument length mismatch: " + pats.mkString(" ") + " and " + args.mkString(" "))
  }

  def apply(cs: Case, args: List[Val], lex: Env): Norm = cs match {
    case Case(pats, body) =>
      norm(body, bind(pats, args, lex))
  }

  def apply(where: Any, cases: List[Case], args: List[Val], lex: Env): Norm = cases match {
    case Nil =>
      fail("no match: " + where + " for " + args.mkString(" "))
    case cs :: rest =>
      { apply(cs, args, lex) } or { apply(where, rest, args, lex) }
  }

  def apply(fun: Curry): Norm = {
    if (fun.isComplete) {
      val cases = fun.cases
      val args = fun.rargs.reverse
      val lex = fun.lex
      apply(fun, cases, args, lex)
    } else {
      fun
    }
  }

  def push(fun: Norm, arg: Val): Norm = fun match {
    case Curry(cases, rargs, lex) => apply(Curry(cases, arg :: rargs, lex))
    case data: Data => Obj(data, arg)
    case _ => sys.error("not a function: " + fun)
  }

  def force(arg: Val): Norm = arg match {
    case defer: Defer => defer.norm
    case norm: Norm => norm
  }

  def defer(expr: Expr, lex: Env): Val = {
    Defer(expr, lex)
  }

  def const(arg: Val): Data = arg match {
    case lzy: Defer => const(lzy.norm)
    case id: Id if isTag(id) => id
    case Obj(fun, arg) => Obj(const(fun), const(arg))
    case fun: Curry => fun // TODO Gidon says we might drop this. Why?
    case _ => sys.error("not constant: " + arg)
  }

  def norm(exprs: List[Expr], lex: Env): List[Norm] = {
    exprs map (norm(_, lex))
  }

  def norm(expr: Expr, lex: Env): Norm = expr match {
    case Wildcard =>
      fail("wildcard in eval")
    case Id("fresh", None) =>
      Id("X", Some(Expr.nextIndex))
    case id: Id if isTag(id) =>
      id
    case id: Id if lex contains id =>
      force(lex(id))
    case id: Id if consts contains id =>
      consts(id)
    case id: Id if funs contains id =>
      Curry(funs(id), Nil, Env.empty)
    case id: Id =>
      fail("unbound identifier: " + id)
    case Lam(cases) =>
      Curry(cases, Nil, lex)
    // Equality is build in and evaluated here
    case Eq(left, right) =>
      if (norm(left, lex) == norm(right, lex)) True
      else False
    case App(fun, arg) =>
      push(norm(fun, lex), defer(arg, lex))
    case let @ Let(_, body) =>
      norm(body, bind(let.pats, norm(let.args, lex), lex))
    case Match(args, cases) =>
      apply(expr, cases, norm(args, lex), lex)
    case Ite(test, left, right) =>
      strict(test, lex) match {
        case True => norm(left, lex)
        case False => norm(right, lex)
        case test => sys.error("not boolean: " + test + " == " + test)
      }
    case _: Bind =>
      fail("unbounded quantifier: " + expr)
  }

  def strict(expr: Expr, lex: Env): Norm = {
    const(norm(expr, lex))
  }
}
