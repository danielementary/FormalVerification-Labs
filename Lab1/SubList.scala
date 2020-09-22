import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.equations._
 import scala.collection.immutable.Stream.Cons
 
object SubList {
 
  def subList[T](l1: List[T], l2: List[T]): Boolean = (l1, l2) match {
    case (Nil(), _)                 => true
    case (_, Nil())                 => false
    case (Cons(x, xs), Cons(y, ys)) => (x == y && subList(xs, ys)) || subList(l1, ys)
  }
 
  // for this one the @induct annotation works but I tried to make it manually as well
  def subListRefl[T](l: List[T]): Unit = {
    l match {
      case Nil() => 
        ()
      case Cons(head, tail) => 
        (
          subList(l,l)                                                      ==:| trivial |:
          subList(Cons(head, tail), Cons(head, tail))                       ==:| trivial |:
          ((head == head && subList(tail, tail)) || subList(l, tail))       ==:| trivial |:
          (subList(tail, tail) || subList(l, tail))                         ==:| subListRefl(tail) |:
          (true || subList(l, tail))                                        ==:| trivial |:
          true
        ).qed
    }
  }.ensuring(_ =>
    subList(l, l)
  )

  def subListLemmaSubset[T](l1: List[T], l2: List[T]): Unit = {
    require(!l2.isEmpty && subList(l1, l2.tail))

  }.ensuring(_ => subList(l1, l2))
 
  def subListTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && subList(l1, l2))

    l1 match {
      case Cons(head1, tail1) if head1 == l2.head && subList(tail1, l2.tail) =>
        (
          subList(l1, l2)                                                                 ==:| trivial |:
          ((l1.head == l2.head && subList(l1.tail, l2.tail)) || subList(l1, l2.tail))     ==:| trivial |:
          ((subList(l1.tail, l2.tail)) || subList(l1, l2.tail))                           ==:| trivial |:
          (subList(l1.tail, l2.tail))                                                     ==:| trivial |:
          subList(l1.tail, l2)                                                            ==:| trivial |:
          true
        ).qed
      case Cons(head1, tail1) if head1 == l2.head && !subList(tail1, l2.tail) =>
        (
          subList(l1, l2)                                                                 ==:| trivial |:
          ((l1.head == l2.head && subList(l1.tail, l2.tail)) || subList(l1, l2.tail))     ==:| trivial |:
          ((subList(l1.tail, l2.tail)) || subList(l1, l2.tail))                           ==:| trivial |:
          subList(l1, l2.tail)                                                            ==:| subListTail(l1, l2.tail) |:
          subList(l1.tail, l2.tail)
        ).qed

      case Cons(head1, tail1) if head1 != l2.head =>
        (
          subList(l1, l2)                                                                 ==:| trivial |:
          ((l1.head == l2.head && subList(l1.tail, l2.tail)) || subList(l1, l2.tail))     ==:| trivial |:
          subList(l1, l2.tail)                                                            ==:| subListTail(l1, l2.tail) |:
          subList(l1.tail, l2.tail)
        ).qed
    }
    
  }.ensuring(_ =>
    subList(l1.tail, l2)
  )
 
  def subListTails[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && l1.head == l2.head && subList(l1, l2))
    if(subList(l1, l2.tail)){
      (
        subList(l1, l2)                                                                 ==:| trivial |:
        ((l1.head == l2.head && subList(l1.tail, l2.tail)) || subList(l1, l2.tail))     ==:| trivial |:
        ((true && subList(l1.tail, l2.tail)) || subList(l1, l2.tail))                   ==:| trivial |:
        (subList(l1.tail, l2.tail) || subList(l1, l2.tail))                             ==:| subListTail(l1, l2.tail) |:                                                        
        (subList(l1.tail, l2.tail) || subList(l1.tail, l2.tail))                        ==:| trivial |:  
        subList(l1.tail, l2.tail)                                                    
      ).qed
    }else{
      (
        subList(l1, l2)                                                                 ==:| trivial |:
        ((l1.head == l2.head && subList(l1.tail, l2.tail)) || subList(l1, l2.tail))     ==:| trivial |:
        ((true && subList(l1.tail, l2.tail)) || subList(l1, l2.tail))                   ==:| trivial |:
        (subList(l1.tail, l2.tail) || subList(l1, l2.tail))                             ==:| trivial |:                                                        
        subList(l1.tail, l2.tail)                                                    
      ).qed
    }
    
  }.ensuring(_ =>
    subList(l1.tail, l2.tail)
  )
 
  def subListTrans[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l3))
    
      (l1, l2, l3) match {
        case (Cons(x, xs), Cons(y, ys), Cons(z, zs)) if(subList(xs,ys) && subList(ys, zs)) =>
          (
            (subList(l1, l2) && subList(l2, l3))                                          ==:| trivial |:
            ((x == y && subList(xs, ys)) || subList(l1, ys) && 
             (y == z && subList(ys, zs)) || subList(l2, zs))                              ==:| trivial |:
            
            ((x == y) && subList(xs, ys) && (y == z) && subList(ys, zs) ||
            (x == y) && subList(xs, ys) && subList(l2, zs) ||
            subList(l1, ys) && (y == z) && subList(ys, zs) ||
            subList(l1, ys) && subList(l2, zs))                                           ==:| trivial |:

            ((x == z) && subList(xs, ys) && subList(ys, zs) ||
            (x == y) && subList(xs, ys) && subList(l2, zs) ||
            subList(l1, ys) && (y == z) && subList(ys, zs) ||
            subList(l1, ys) && subList(l2, zs))                                           ==:| subListTrans(xs, ys, zs) |:

            ((x == z) && subList(xs, zs) ||
            (x == y) && true && subList(l2, zs) ||
            subList(l1, ys) && (y == z) && true ||
            subList(l1, ys) && subList(l2, zs))                                           ==:| trivial |:

            ((x == z) && subList(xs, zs) ||
            (x == y) && subList(l2, zs) ||
            subList(l1, ys) && (y == z) ||
            subList(l1, ys) && subList(l2, zs))                                           ==:| trivial |:

            ((x == z) && subList(xs, zs) ||
            subList(l1, ys) && (y == z) ||
            (subList(l2, zs) && ((x == y) || (x != y) && subList(l1, ys))))               ==:| trivial |:

            ((x == z) && subList(xs, zs) ||
            subList(l1, ys) && (y == z) ||
            (subList(l2, zs) && ((x == y) || subList(xs, ys))))                           ==:| trivial |:

            ((x == z) && subList(xs, zs) ||
            subList(l1, ys) && (y == z) ||
            (subList(l2, zs) && ((x == y) || true)))                                      ==:| trivial |:

            ((x == z) && subList(xs, zs) ||
            subList(l1, ys) && (y == z) && subList(ys, zs) ||
            subList(l2, zs))                                                              ==:| trivial|:

            ((x == z) && subList(xs, zs) ||
            subList(l1, ys) && (y == z) && true||
            subList(l2, zs))                                                              ==:| trivial|:

            ((x == z) && subList(xs, zs) ||
            subList(l1, ys) && (y == z) ||
            subList(l2, zs))                                                              ==:| trivial|:

            ((x == z) && subList(xs, zs) ||
            subList(l1, ys) && (y == z) ||
            subList(l2, zs))                                                              ==:| trivial|:
            
            ((x == z && subList(xs, zs)) || subList(l1, zs))                              ==:| trivial |:
            subList(l1, l3)
          ).qed

        case  _ => ()
      }
    
  }.ensuring(_ =>
    subList(l1, l3)
  )

  def tailSmallerThanListLemma[T](l1: List[T]): Unit = {
    require(!l1.isEmpty)
  }.ensuring(_ => l1.tail.length <= l1.length)
 
  def subListLength[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2))

    (l1, l2) match {
      case (Cons(x,xs), Cons(y,ys))  =>
        assert(subList(l1, l2))
        assert((x == y && subList(xs, ys)) || subList(l1, ys))
        if((x == y && subList(xs, ys))){
          assert((x == y && subList(xs, ys)))
          assert(subList(xs, ys))
          subListLength(xs, ys)
          assert(xs.length <= ys.length)
          assert(xs.length + 1 <= ys.length + 1)
          assert(l1.length <= l2.length)
        } else{
            assert(subList(l1, ys))
            subListLength(l1, ys)
            assert(l1.length <= ys.length)
            assert(l1.length <= ys.length + 1)
            assert(l1.length <= l2.length)
        }
      case _ =>
        ()
    }
  }.ensuring(_ =>
    l1.length <= l2.length
  )
 
  def subListEqual[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2) && l1.length >= l2.length)
    subListLength(l1, l2)
    assert(l1.length <= l2.length)
    assert(l1.length == l2.length)

    (l1, l2) match {
      case (Cons(x, xs), Cons(y,ys)) =>
        assert(subList(l1, l2))
        assert((x == y && subList(xs, ys)) || subList(l1, ys))
        if(x == y && subList(xs, ys)){
          assert(subList(xs, ys))
          subListEqual(xs, ys)
          assert(xs == ys)
          assert(l1 == l2)
        }
      case _ =>
        ()
    }

  }.ensuring(_ =>
    l1 == l2
  )
 
  def subListAntisym[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l1))
    
    //TODO
    assume(l1 == l2)

  }.ensuring(_ =>
    l1 == l2
  )
 
  @extern 
  def assume(b: Boolean): Unit = {

  }ensuring(_ => b)
  @extern
  def main(args: Array[String]): Unit = {
    println(subList(List(0, 2), List(0, 1, 2))) // true
    println(subList(List(1, 0), List(0, 0, 1))) // false
    println(subList(List(10, 5, 25), List(70, 10, 11, 8, 5, 25, 22))) // true
  }
 
}
