import _root_.KTDCW.Task1to5.BTree

/**
  * Created by jester on 1/19/16.
  */

//import org.scalacheck._
//import Prop._
//import akka.actor._

object KTDCW extends App {
  println("heloo")
  //--------------------------------------------------------------------
  // 2015
  def exists(p: Int, as: List[Int]): Boolean = as match
  {
    case Nil => false
    case x::xs => p(x) || exists(p, xs)
  }

  case object Empty extends BTree[Nothing]
  case class Node[T](left: BTree[T], right: BTree[T]) extends BTree[T]
  case class Leaf[T](e: T) extends BTree[T]

  def treeMap[A,B](f : A => B)(tree : BTree[A]): BTree[B] = tree match {
    case Leaf(e)   => Leaf(f(e))
    case Node(l,r) => Node(treeMap(f)(l), treeMap(f)(r))
  }



  //=====================================================================
  object Task1to5 {

    // 1.1
    def harm(l: List[Int]): Double  = {
      def harmRec(l: List[Int], sum: Double, len: Int): Double = l match {
        case x::_  if (x == 0) => 0.0
        case Nil   => if (len != 0) (len / sum) else 0.0
        case x::xs => harmRec(xs, sum + 1.0 / x, len + 1)
      }
      harmRec(l, 0.0, 0)
    }


    // 1.2
    def sum2(l: List[Int]): Int = {
      def sum2Rec(l: List[Int], sum: Int): Int = l match {
        case Nil => sum
        case x::xs => sum2Rec(xs, sum + x)
      }
      sum2Rec(l, 0)
    }


    // 1.3
    def sumG[T](m: (T,T) => T)(n: T)(l: List[T]): T = {
      def add(l: List[T], sum: T): T = l match {
        case Nil => sum
        case x::xs => add(xs, m(sum,x))
      }
      add(l, n)
    }

    def sum2 = sumG((x: Int, y: Int) => x + y) (0) _
    //def concat = sumG((x: String, y: String) => x + y) ("") _


    // 1.4
    def span[T](p: T => Boolean, l: List[T]): (List[T], List[T]) = {
      def spanRec(l: List[T], l1: List[T], l2: List[T]): (List[T], List[T]) = l match {
        case Nil   => (l1,l2)
        case x::xs => if (p(x)) spanRec(xs, l1:+x, l2) else (l1, l)
      }
      spanRec(l, Nil, Nil)
    }

    //def intSpan(l: List[Int]) = span(((x: Int) => (x < 5)), l)


    // 1.5
    def append[T](as: List[T], bs: List[T]): List[T] = as match {
      case Nil => bs
      case x::xs => x::append(xs, bs)
    }

    def reverse[T](l: List[T]): List[T] = l match {
      case Nil => Nil
      case x::xs => append(reverse(xs), x::Nil)
    }

    /*def reverse[T](l: List[T]): List[T] = l match {
      case Nil => Nil
      case x::xs => reverse(xs):+x
    }*/



    // 2.1
    // Fügen Sie hier den Beweis in Kommentaren ein:

    // Beweisen Sie das: length(reverse(as)) = length(as)

    // Basisfall (we substitute Nil for as in P):
    // length(reverse(Nil))
    // = length(Nil)         [def reverse l.r.]

    // Induktionsschritt (we extend as with a::as in P):
    // length(reverse(a::as))
    // = length(append(reverse(as), a::Nil))    [def reverse l.r.]
    // = length(reverse(as)) + length(a::Nil)   [proved in lecture]
    // = length(as) + length(a::Nil)            [induction hypothesis P l.r.]
    // = length(as) + 1 + length(Nil)           [def length l.r.]
    // = length(as) + 1 + 0                     [def length l.r.]
    // = length(as) + 1                         [arithmetic]
    // = 1 + length(as)                         [arithmetic commutative]
    // = lenght(a::as)                          [def length r.l.]


    // 2.2
    // Fügen Sie hier den Beweis in Kommentaren ein:

    // Beweisen Sie das: sum(l) = sum2(l)

    // Basisfall (we substitute Nil for as in P):
    // sum(Nil)
    // = 0            [def sum l.r.]
    // = add(Nil, 0)  [def add r.l.]
    // = sum2(Nil)    [def sum2 r.l.]

    // Induktionsschritt (we extend as with a::as in P):
    // sum(a::as)
    // = a + sum(as)                          [def sum l.r.]
    // = a + sum2(as)                         [induction hypothesis P l.r.]
    // = a + add(as, 0)                       [def sum2 l.r.]
    // = add(as, 0 + a)                       [def add r.l.]
    // = sum2(a::as)                          [def sum2 r.l.]


    // 2.* (Bonus)
    // Beweisen Sie das: reverse(append(as, bs)) = append(reverse(bs), reverse(as))

    // Basisfall (we substitute Nil for as in P):
    // reverse(append(Nil, bs))
    // = reverse(bs)                          [def append l.r.]
    // = append(reverse(bs), Nil)             [def append r.l.]
    // = append(reverse(bs), reverse(Nil))    [def reverse r.l.]

    // Induktionsschritt (we extend as with a::as in P):
    // reverse(append(a::as, bs))
    // = reverse(a::append(as, bs))           [def append l.r.]
    // = reverse(append(as, bs)):+a           [def reverse l.r.]
    // = append(reverse(bs), reverse(as)):+a  [induction hypothesis P l.r.]
    // = append(reverse(bs), reverse(as):+a)  [def append r.l.]
    // = append(reverse(bs), reverse(a::as))  [def reverse r.l.]



    // 3.1
    def mergeList(l1 : List[Int], l2 : List[Int], lm : List[Int]) : List[Int] = l1 match {
      case Nil => l2 match {
        case Nil => Nil
        case _ => lm:::l2
      }
      case x::xs => l2 match {
        case Nil => lm:::l1
        case y::ys => if (x > y) mergeList(x::xs, ys, lm:+y) else mergeList(xs, y::ys, lm:+x)
      }
    }

    def mergeSort(split : List[Int] => (List[Int], List[Int]), l: List[Int]): List[Int] = split(l) match {
      case (Nil, Nil) => Nil
      case (x::Nil, Nil) => x::Nil
      case (Nil, y::Nil) => y::Nil
      case (x::Nil, y::Nil) => mergeList(x::Nil, y::Nil, Nil)
      case (x::xs, Nil) => mergeSort(split, x::xs)
      case (Nil, y::ys) => mergeSort(split, y::ys)
      case (x::xs, y::ys) => mergeList(mergeSort(split, x::xs), mergeSort(split, y::ys), Nil)
    }

    /*def splitInt(l: List[Int]): (List[Int], List[Int]) = {
      val n = l.length / 2
      (l.take(n), l.drop(n))
    }

    def mergeInts(l: List[Int]) = mergeSort(splitInt, l)*/


    // 3.2
    def mergeListG[T](p : (T,T) => Boolean)(l1 : List[T], l2 : List[T], lm : List[T]) : List[T] = l1 match {
      case Nil => l2 match {
        case Nil => Nil
        case _ => lm:::l2
      }
      case x::xs => l2 match {
        case Nil => lm:::l1
        case y::ys => if (p(x, y)) mergeListG(p)(x::xs, ys, lm:+y) else mergeListG(p)(xs, y::ys, lm:+x)
      }
    }

    def mergeSortG[T](p: (T,T) => Boolean, split : List[T] => (List[T], List[T]))(l: List[T]): List[T] = split(l) match {
      case (Nil, Nil) => Nil
      case (x::Nil, Nil) => x::Nil
      case (Nil, y::Nil) => y::Nil
      case (x::Nil, y::Nil) => mergeListG(p)(x::Nil, y::Nil, Nil)
      case (x::xs, Nil) => mergeSortG(p, split)(x::xs)
      case (Nil, y::ys) => mergeSortG(p, split)(y::ys)
      case (x::xs, y::ys) => mergeListG(p)(mergeSortG(p, split)(x::xs), mergeSortG(p, split)(y::ys), Nil)
    }

    /*def splitString(l: List[String]): (List[String], List[String]) = {
      val n = l.length / 2
      (l.take(n), l.drop(n))
    }

    def mergeIntsG = mergeSortG(((x: Int, y: Int) => (x > y)), splitInt) _
    def mergeStringsG = mergeSortG(((x: String, y: String) => (x > y)), splitString) _*/


    // 3.3
    def split (l: List[Int]): (List[Int], List[Int]) = {
      val n = l.length / 2
      (l.take(n), l.drop(n))
    }
//
//    def propSplit = forAll { (as : List[Int]) =>
//      val (bs : List[Int], cs : List[Int]) = split(as)
//      (bs.length + cs.length) == as.length
//    }
//
//
//    // 3.4
//    def propSort = forAll {
//      (as : List[Int]) => mergeSort(split, as) == isort(as)
//    }



    // 4.1
    def exists[T](p: T => Boolean, xs: List[T]): Boolean =
      xs.foldRight(false)((a: T, b: Boolean) => b || p(a))

    //def existsInt(l: List[Int]) = exists(((a: Int) => a > 100), l)


    // 4.2
    def max(l: List[Int]): Int =
      l.foldRight(Integer.MIN_VALUE)((a: Int, b: Int) => if (a > b) a else b)


    // 4.3
    def mapF[A, B](f: A => B)(xs: List[A]): List[B] =
      xs.foldLeft(List[B]())((b: List[B], a: A) => b:+f(a))
    //def mapF1[A, B](f: A => B)(xs: List[A]): List[B] =
    //xs.foldRight(List[B]())((a: A, b: List[B]) => f(a)::b)


    // 4.4
    def partition[T](p: T => Boolean, xs: List[T]): (List[T],List[T]) =
      xs.foldLeft((List[T](),List[T]()))((b: (List[T], List[T]), a: T) =>
        if (p(a)) (b._1:+a, b._2) else (b._1, b._2:+a))


    // 4.5
    def insert(e: Int, as: List[Int]): List[Int] = {
      val bs: (List[Int], Boolean) =
        as.foldLeft((List[Int](), false))((b: (List[Int], Boolean), a: Int) =>
          if (!b._2 && e <= a) (b._1:+e:+a, true) else (b._1:+a, b._2))
      if (bs._2 == false) bs._1:+e else bs._1
    }

    def isort(l: List[Int]): List[Int] =
      l.foldLeft(List[Int]())((b: List[Int], a: Int) => insert(a, b))



    // 5.1
    abstract class BExp
    case object True extends BExp
    case object False extends BExp
    case class  Variable(id: String) extends BExp
    case class  Not(b: BExp) extends BExp
    case class  Or(left: BExp, right: BExp) extends BExp
    // extend here
    case class XOr(left: BExp, right: BExp) extends BExp
    case class Implication(left: BExp, right: BExp) extends BExp


    // 5.2
    def simplify(b: BExp): BExp = b match {
      case Or(True,r)  => True
      case Or(l,True)  => True
      case Or(False,r) => simplify(r)
      case Or(l,False) => simplify(l)
      case Not(Not(e)) => simplify(e)
      // extend here
      //case Or(l, r) => simplify(Or(simplify(l), simplify(r)))
      case XOr(False, r) => simplify(r)
      case XOr(l, False) => simplify(l)
      case XOr(True, r) => simplify(Not(r))
      case XOr(l, True) => simplify(Not(l))
      //case XOr(l, r) => simplify(XOr(simplify(l), simplify(r)))
      case Implication(False, r) => True
      case Implication(l, False) => simplify(Not(l))
      case Implication(True, r) => simplify(r)
      case Implication(l, True) => simplify(Implication(simplify(l),True))
      //case Implication(l, r) => simplify(Implication(simplify(l), simplify(r)))
      case _ => b
    }


    // 5.3
    abstract class BTree[+T]

    // Doesn't work properly -> Therfore need to run propTree.check without Nil!
    /*{
      def +[T](that: T) = Empty
    }*/

    // extend here
    case object Empty extends BTree[Nothing]
    case class Node[T](left: BTree[T], right: BTree[T]) extends BTree[T]
    case class Leaf[T](e: T) extends BTree[T]


    // 5.4
    def treeMap[A,B](f : A => B)(tree : BTree[A]): BTree[B] = tree match {
      case Leaf(e)   => Leaf(f(e))
      case Node(l,r) => Node(treeMap(f)(l), treeMap(f)(r))
    }

    //val tree = Node(Node(Leaf(3), Leaf(4)), Node(Node(Leaf(5), Leaf(8)), Node(Leaf(13), Leaf(14))))


    // 5.5
    /*def treeToList[T](tree : BTree[T]): List[T] = tree match {
      case Leaf(e)    => List[T](e)
      case Node(l, r) => treeToList(l):::treeToList(r)
    }*/


    // 5.* (Bonus)
    def treeToList[T](tree : BTree[T]) : List[T] = treeFold(tree)(List[T]())(
      (a: T, b: List[T]) => b:::List(a)
    )

    def treeFold[A, B](as: BTree[A])(e: B)(f: (A,B) => B) : B = as match {
      case Leaf(a)    => f(a, e)
      case Node(l, r) => treeFold(r)(treeFold(l)(e)(f))(f)
    }

    def splitG[T](l: List[T]): (List[T], List[T]) =
      (l.take(l.length / 2), l.drop(l.length / 2))

    def makeTree[T](l: List[T]): BTree[T] = l match {
      case Nil => Empty
      case x::Nil => Leaf(x)
      case x::xs => val (as : List[T], bs : List[T]) = splitG(l); Node(makeTree(as), makeTree(bs))
    }

    // compose gives error (Asked in NG but not answered)
    // val l1 = treeToList[Int] _ compose treeMap(f)(t)
//    def propTree = forAll { as : List[Int] =>
//      as != Nil ==> (treeToList(treeMap((x: Int) => x + 1)(makeTree(as))) ==
//        treeToList(makeTree(as)).map((x: Int) => x + 1))
//    }
  }


  // 6
  // Define here actor classes
  abstract class Message
  case class  Play(n: Int) extends Message
  case object PingM  extends Message
  case object PongM  extends Message
  case object Stop  extends Message

//  class Server(an: Int) extends Actor {
//
//    var stop = false
//
//    def receive = {
//      case Play(n) => println("Server started")
//        context.system.actorOf(Props(classOf[Client],n-1, self.path.name), "c" + (n - 1));
//      case PingM => if(!stop) {
//        println("Server: Ping" )
//        context.system.actorSelection("/user/c" + (an - 1)) ! PongM
//      }
//      else {
//        println("Server stops!")
//        context.system.actorSelection("/user/c" + (an - 1)) ! Stop;
//        context.stop(self)
//      }
//      case Stop => stop = true
//    }
//  }
//
//  class Client(name: Int, creator: String) extends Actor {
//    println(name)
//    println(self.path.name)
//    if(name > 0)
//      context.system.actorOf(Props(classOf[Client],name - 1, self.path.name),"c" + (name - 1))
//    else
//      context.system.actorSelection("/user/c" + (name + 1)) ! PingM
//    def receive = {
//      case PingM  => println(self.path.name + ": Ping" )
//        context.system.actorSelection("/user/" + creator) ! PingM
//      case PongM  => println(self.path.name + ": Pong" )
//        if(!name.equals(0))
//          context.system.actorSelection("/user/c" + (name - 1)) ! PongM
//        else
//          context.system.actorSelection("/user/" + creator) ! PingM
//      case Stop  => if(name > 0) {
//        println(self.path.name + ": Pong stops!")
//        context.system.actorSelection("/user/c" + (name - 1)) ! Stop
//        context.stop(self)
//      }
//      else {
//        println(self.path.name + ": Pong stops!")
//        context.stop(self)
//      }
//    }
//  }
//
//  object Main extends App {
//    val n = 10000 // the number of clients (try increasing to 10000 minimum :)
//    println("Creating the Server")
//    val system = ActorSystem("Hello")
//
//    println("Creating " + n + " Clients")
//    val serv = system.actorOf(Props(classOf[Server], n));
//
//    println("Start playing ...")
//    serv ! Play(n)
//    Thread.sleep(10000)
//    println("Stop playing ...")
//    serv ! Stop
//  }

}
//