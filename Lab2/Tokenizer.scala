import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.equations._
import stainless.proof.check
 
object Tokenizer {
 
  /************************************************************************************************/
  /* Part 1: Parser                                                                               */
  /************************************************************************************************/
 
  case class Parser[A](parse: List[Token] => Option[(A, List[Token])]) {
    def flatMap[B](f: A => Parser[B]): Parser[B] = Parser(ts => parse(ts).flatMap {
      case (x, rs) => f(x).parse(rs)
    })
  }
 
  def pure[A](x: A): Parser[A] = Parser((ts: List[Token]) => Some((x, ts)))
 
  def leftIdentity[A, B](a: A, f: A => Parser[B], ts: List[Token]): Unit = {
    ()
  }.ensuring(_ =>
    pure(a).flatMap(f).parse(ts) == f(a).parse(ts)
  )
 
  def rightIdentity[A, B](a: A, f: A => Parser[B], ts: List[Token]): Unit = {
    ()
  }.ensuring(_ =>
    pure(a).flatMap(pure).parse(ts) == pure(a).parse(ts)
  )
 
  def associativity[A, B, C](a: A, f: A => Parser[B], g: B => Parser[C], ts: List[Token]): Unit = {
    ()
  }.ensuring(_ =>
    pure(a).flatMap(f).flatMap(g).parse(ts) == pure(a).flatMap(x => f(x).flatMap(g)).parse(ts)
  )
 
  /************************************************************************************************/
  /* Part 2: Tokenizer                                                                            */
  /************************************************************************************************/
 
  sealed abstract class Token {
    def chars: List[Char]
  }
 
  case class Identifier(cs: List[Char]) extends Token {
    override def chars = cs
  }
 
  case object Open extends Token {
    override def chars = List('(')
  }
 
  case object Close extends Token {
    override def chars = List(')')
  }
 
  def isLowerCase(c: Char): Boolean = 'a' <= c && c <= 'z'
 
  def parsableCharacter(c: Char): Boolean = c == ' ' || c == '(' || c == ')' || isLowerCase(c)
 
  def parsableToken(t: Token): Boolean = t match {
    case Identifier(cs) => cs.forall(isLowerCase) && !cs.isEmpty
    case _ => true
  }
 
  @opaque
  def dropWhileForall[T](@induct l: List[T], p1: T => Boolean, p2: T => Boolean): Unit = {
    require(l.forall(p1))
    ()
  }.ensuring(_ => l.dropWhile(p2).forall(p1))
 
  def tokenize(cs: List[Char]): List[Token] = {
    require(cs.forall(parsableCharacter))
    decreases(cs.length)
 
    cs match {
      case Nil() => Nil()
      case Cons(c, cs) if c == ' ' => tokenize(cs)
      case Cons(c, cs) if c == '(' => Open :: tokenize(cs)
      case Cons(c, cs) if c == ')'  => Close :: tokenize(cs)
      case Cons(c, cs2) if isLowerCase(c) =>
        val id = cs.takeWhile(isLowerCase)
        val rest = cs.dropWhile(isLowerCase)
 
        dropWhileForall(cs, parsableCharacter, isLowerCase)
 
        Identifier(id) :: tokenize(rest)
    }
  }
 
  def lowerCaseCharsAreParsableLemma(cs: List[Char]): Unit = {
    require(cs.forall(isLowerCase))

    cs match {
      case Cons(c, cs2) =>
        (
          cs.forall(isLowerCase)                                                              ==:| trivial |:
          (isLowerCase(c) && cs2.forall(isLowerCase))                                         ==:| trivial |:
          ((isLowerCase(c) || false) && cs2.forall(isLowerCase))                              ==:| trivial |:
          ((isLowerCase(c) || c == ' ' || c == '(' || c == ')') && cs2.forall(isLowerCase))   ==:| trivial |:
          (parsableCharacter(c) && cs2.forall(isLowerCase))                                   ==:| lowerCaseCharsAreParsableLemma(cs2) |:
          (parsableCharacter(c) && cs2.forall(parsableCharacter))                             ==:| trivial |:
          cs.forall(parsableCharacter)
        ).qed
      case _ => ()
    }
  }.ensuring(_ => cs.forall(parsableCharacter))

  def parsableTokenMeansParsableChars(t: Token): Unit = {
    require(parsableToken(t))

    t match {
      case Identifier(cs) => {
        assert(parsableToken(t))
        assert(cs.forall(isLowerCase) && !cs.isEmpty)
        assert(cs.forall(isLowerCase))
        lowerCaseCharsAreParsableLemma(cs)
        assert(cs.forall(parsableCharacter))
      }
      case _ => ()
    }
  }.ensuring(_ => t.chars.forall(parsableCharacter))

  def concatLemma(l1: List[Char], l2: List[Char]): Unit = {
    require(l1.forall(parsableCharacter) && l2.forall(parsableCharacter))

    (l1, l2) match {
      case (Cons(c1, cs1), _) => 
        (
          (l1.forall(parsableCharacter) && l2.forall(parsableCharacter))                           ==:| trivial |:
          (parsableCharacter(c1) && cs1.forall(parsableCharacter) && l2.forall(parsableCharacter)) ==:| concatLemma(cs1, l2) |:
          (parsableCharacter(c1) && (cs1 ++ l2).forall(parsableCharacter))                         ==:| trivial |:
          (Cons(c1, cs1 ++ l2)).forall(parsableCharacter)                                          ==:| trivial |:
          (Cons(c1, cs1) ++ l2).forall(parsableCharacter)                                          ==:| trivial |:
          (l1 ++ l2).forall(parsableCharacter)
        ).qed
      case _ => ()
    }
  }.ensuring( _ => (l1 ++ l2).forall(parsableCharacter))

  def charsListPlusSpaceIsStillParsable(l: List[Char]): Unit = {
    require(l.forall(parsableCharacter))

    assert(List(' ').forall(parsableCharacter))
    concatLemma(l, List(' '))

  }.ensuring(_ => (l ++ List(' ')).forall(parsableCharacter))

  def superLemma(ts: List[Token]): Unit = {
    require(ts.forall(parsableToken))

    ts match {
      case Cons(t, ts2) =>
        assert(ts.forall(parsableToken))
        assert(parsableToken(t) && ts2.forall(parsableToken))

        parsableTokenMeansParsableChars(t)
        superLemma(ts2)
        assert(t.chars.forall(parsableCharacter) && ts2.flatMap(t => t.chars ++ List(' ')).forall(parsableCharacter))

        charsListPlusSpaceIsStillParsable(t.chars)
        assert((t.chars ++ List(' ')).forall(parsableCharacter) && ts2.flatMap(t => t.chars ++ List(' ')).forall(parsableCharacter))

        concatLemma((t.chars ++ List(' ')), ts2.flatMap(t => t.chars ++ List(' ')))
        assert(((t.chars ++ List(' ')) ++ ts2.flatMap(t => t.chars ++ List(' '))).forall(parsableCharacter))
        assert(ts.flatMap(t => t.chars ++ List(' ')).forall(parsableCharacter))
      case _ => ()
    }
  }.ensuring(_ => ts.flatMap(t => t.chars ++ List(' ')).forall(parsableCharacter))
 
  def isLowerCaseThenNotSpace(l: List[Char]): Unit = {
    require(l.forall(isLowerCase))
    l match {
      case Nil() => 
      case Cons(c, cs) =>
        (
          l.forall(isLowerCase)                                                 ==:| trivial |:
          (isLowerCase(c) && cs.forall(isLowerCase))                            ==:| trivial |:
          (('a' <= c && c <= 'z') && cs.forall(isLowerCase))                    ==:| isLowerCaseThenNotSpace(cs) |:
          ((c != ' ') && cs.forall( v => v != ' '))                             ==:| trivial |:
          l.forall(v => v != ' ')
        ).qed
    }
    
  }.ensuring(_ => l.forall(c => c != ' '))
  def tokenNotContainSpace(t: Token) : Unit = {
    require(parsableToken(t))
    
    t match {
      case Identifier(cs) => {
        assert(cs.forall(isLowerCase) && !cs.isEmpty)
        isLowerCaseThenNotSpace(cs)
        assert(cs.forall(v => v != ' '))
      }
      case _ => 
    }
  }.ensuring(_ => t.chars.forall(c => c != ' '))

  def testLemma(l1: List[Char], l2: List[Char]): Unit = {
    require(l1.forall(isLowerCase) && l1.forall(c => c != ' '))
    
    val call = l1.takeWhile(isLowerCase)

    l1 match {
      case Cons(h,t) if isLowerCase(h) => {
        assert(Cons(h, t.takeWhile(isLowerCase)) == l1.takeWhile(isLowerCase)) 
        testLemma(t, l2)
      }
      case _ => 
    }
  }.ensuring( _ => (l1 ++ List(' ') ++ l2).takeWhile(isLowerCase) == l1 && (l1 ++ List(' ') ++ l2).dropWhile(isLowerCase) == List(' ') ++ l2)

  def superConcatLemma(t: Token, ts: List[Token]): Unit = {
    require((t :: ts).forall(parsableToken) && ((t.chars ++ List(' ')) ++ ts.flatMap(t => t.chars ++ List(' '))).forall(parsableCharacter) && (ts.flatMap(t => t.chars ++ List(' '))).forall(parsableCharacter))
    
    val l = (t :: ts).flatMap(t => t.chars ++ List(' '))
    l match {
      case Nil() => ()
      case Cons(c, cs) => {
        assert(Cons(c, cs) == t.chars ++ List(' ') ++ ts.flatMap(t => t.chars ++ List(' ')))
        Cons(c, cs) match {
          case Cons(c2, cs2) if c2 == ' ' => 
          case Cons(c2, cs2) if c2 == '(' => 
          case Cons(c2, cs2) if c2 == ')'  => 
          case Cons(c2, cs2) if isLowerCase(c2) =>
            val id = l.takeWhile(isLowerCase)
            val rest = l.dropWhile(isLowerCase)

            tokenNotContainSpace(t)
            assert(t.chars.forall(isLowerCase))
            assert(t.chars.forall(c => c != ' '))
            testLemma(t.chars, ts.flatMap(t => t.chars ++ List(' ')))

            assert(rest.forall(parsableCharacter))

            assert(Identifier(id) :: tokenize(rest) == Identifier(t.chars) :: tokenize(rest))
            assert(Identifier(t.chars) :: tokenize(rest) == Identifier(t.chars) :: tokenize((ts.flatMap(t => t.chars ++ List(' ')))))
            assert(Identifier(t.chars) :: tokenize((ts.flatMap(t => t.chars ++ List(' ')))) == List(t) ++ tokenize(ts.flatMap(t => t.chars ++ List(' '))))
          }
      }   
    }

  }.ensuring(_ => tokenize((t.chars ++ List(' ')) ++ ts.flatMap(t => t.chars ++ List(' '))) == (List(t) ++ tokenize(ts.flatMap(t => t.chars ++ List(' ')))))

  @opaque
  def retokenizeTokens(ts: List[Token]): Unit = {
    require(ts.forall(parsableToken))
    decreases(ts)
 
    superLemma(ts)
    assert(ts.flatMap(t => t.chars ++ List(' ')).forall(parsableCharacter))
 
    ts match {
      case Nil() => ()
      case Cons(t, ts2) =>
        (
          tokenize(ts.flatMap(t => t.chars ++ List(' '))) ==:| trivial |: // by definiton of flatMap
          tokenize((t.chars ++ List(' ')) ++ ts2.flatMap(t => t.chars ++ List(' '))) ==:| superConcatLemma(t, ts2) |:
          List(t) ++ tokenize(ts2.flatMap(t => t.chars ++ List(' '))) ==:| retokenizeTokens(ts2) |:
          List(t) ++ ts2 ==:| trivial |:
          ts
        ).qed
    }
 
  }.ensuring(_ => tokenize(ts.flatMap(t => t.chars ++ List(' '))) == ts)
 
  @extern
  def main(args: Array[String]) = {
 
    def scalaListToStainlessList[T](l: scala.collection.immutable.List[T]): List[T] = l match {
      case scala.collection.immutable.Nil => Nil()
      case scala.collection.immutable.::(x, xs) => Cons(x, scalaListToStainlessList(xs))
    }
 
    def stainlessListToScalaList[T](l: List[T]): scala.collection.immutable.List[T] = l match {
      case Nil()        => scala.collection.immutable.Nil
      case Cons(x, xs)  => scala.collection.immutable.::(x, stainlessListToScalaList(xs))
    }
 
    val tokens = stainlessListToScalaList(tokenize(scalaListToStainlessList(args(0).toList)))
    println("tokens: " + tokens.mkString(" "))
  }
}
