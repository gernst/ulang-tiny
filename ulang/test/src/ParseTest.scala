import org.scalatest.funspec.AnyFunSpec
import ulang.{Parse => p}
import arse.Input

class ParseCommentsTest extends AnyFunSpec {
  // We put these test in a seerate class in order to seerate the imports for
  // the implicit whitespace handling.  This class should explicitly test some
  // features of this whitespace parser.

  def mkInput(string: String) = new Input(string, 0, p.whitespace)

  describe("Comments") {
    describe("Extend to the end of line") {
      it("part one") {
        val input = mkInput("//eval Foo;\n")
        assert(p.script.parseAll(input) == Nil)
      }

      it("part two") {
        val input = mkInput("//eval Foo;\neval Foo;")
        val actual = p.script.parseAll(input)
        val expected = List(ulang.Evals(List(ulang.Id("Foo"))))
        assert(actual == expected)
      }
    }
  }
}

class ParseTest extends AnyFunSpec {
  // We import the automatic conversion String -> arse.Input.
  import arse._
  implicit val w = p.whitespace

  describe("Fixity expressions") {
    it("for prefix operators") {
      val (names, fixity) = p.fix.parse("opname [prefix 5]")
      assert(names == List("opname"))
      assert(fixity == Prefix(5))
    }
    it("for postfix operators") {
      val (names, fixity) = p.fix.parse("opname [postfix 5]")
      assert(names == List("opname"))
      assert(fixity == Postfix(5))
    }
    it("for infix operators") {
      val (names, fixity) = p.fix.parse("opname [infix 5]")
      assert(names == List("opname"))
      assert(fixity == Infix(Non, 5))
    }
    it("accept several operator names") {
      val (names, fixity) = p.fix.parse("op1 op2 op3 [infix 42]")
      assert(names == List("op1", "op2", "op3"))
      assert(fixity == Infix(Non, 42))
    }
  }

  describe("let expressions") {
    import ulang.{Let, Case1, Id, App}
    it("can define simple bindings") {
      val actual = p.let.parse("let x = y in x")
      assert(actual == Let(List(Case1(Id("x"), Id("y"))), Id("x")))
    }
    it("can bind several names, separated by ;") {
      val actual = p.let.parse("let x = y; a = b in x a")
      assert(actual == Let(List(Case1(Id("x"), Id("y")),
                                Case1(Id("a"), Id("b"))),
                           App(Id("x"), Id("a"))))
    }
    it("can be nested on both sides") {
      val actual = p.let.parse("""
        let x = let a = A;
                    b = B
                in a b
        in let y = Z
           in x y""")
      val expected = Let(List(Case1(Id("x"), Let(List(Case1(Id("a"), Id("A")),
                                                      Case1(Id("b"), Id("B"))),
                                                 App(Id("a"), Id("b"))))),
                         Let(List(Case1(Id("y"), Id("Z"))),
                             App(Id("x"), Id("y"))))
      assert(actual == expected)
    }
  }

  describe("match expressions") {
    import ulang.{Match, Case, Id, App}
    it("can match one case") {
      val actual = p.mtch.parse("match x with A -> B")
      assert(actual == Match(List(Id("x")),
                             List(Case(List(Id("A")), Id("B")))))
    }
  }

  describe("lambda expressions") {
    import ulang.{Lam, Case, Id, App}
    it("can have one simple argument") {
      val actual = p.lam.parse("lambda x -> x")
      assert(actual == Lam(List(Case(List(Id("x")), Id("x")))))
    }
  }
}
