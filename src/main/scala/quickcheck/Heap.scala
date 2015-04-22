package quickcheck

import common._

trait IntHeap extends Heap {
  override type A = Int
  override def ord = scala.math.Ordering.Int
}

// http://www.brics.dk/RS/96/37/BRICS-RS-96-37.pdf

// Figure 1, page 3
trait Heap {
  type H // type of a heap
  type A // type of an element // rw: what relation to a Node, exactly?
  def ord: Ordering[A] // ordering on elements

  def empty: H // the empty heap
  def isEmpty(h: H): Boolean // whether the given heap h is empty

  def insert(x: A, h: H): H // the heap resulting from inserting x into h
  def meld(h1: H, h2: H): H // the heap resulting from merging h1 and h2

  def findMin(h: H): A // a minimum of the heap h
  def deleteMin(h: H): H // a heap resulting from deleting a minimum of h
}

// Figure 3, page 7
// A BinomialHeap is a forest of binomial trees.
trait BinomialHeap extends Heap {

  type Rank = Int
  case class Node(x: A, r: Rank, c: List[Node]) // x is data value (basis) for priority. c is children
  override type H = List[Node] // nodes

  protected def root(t: Node) = t.x // What is this? A query? No logic to determine (evaluate) or establish the basis for a particular node to be a root.
  protected def rank(t: Node) = t.r // Again, no logic apparent. Why is this in Binomial Heap? 
  
  // Join two trees of equal rank (and size) by descending data value (basis of priority, i.e. min)
  protected def link(t1: Node, t2: Node): Node = // t1.r==t2.r
    if (ord.lteq(t1.x, t2.x)) Node(t1.x, t1.r+1, t2::t1.c) else Node(t2.x, t2.r+1, t1::t2.c)
  
  // insert a node into the BinomialHeap (ascending in rank), recursive
  protected def ins(t: Node, ts: H): H = ts match {
    case Nil => List(t)
    case tp :: ts => // t.r<=tp.r // rw: I don't see where any ordering is enforced yet, implicitly or otherwise.
      if (t.r < tp.r) t :: tp :: ts else ins(link(t, tp), ts) // rw: I've proved the logic of this to myself (i.e. because of ordering, if t.r is not less than tp.r then, because of ordering, it must have equivalent ranking.
  }

  override def empty = Nil
  override def isEmpty(ts: H) = ts.isEmpty

  // Encapsulate a data value into a Node. Insert the Node into the a List[Nodes] (i.e. typically H (heap) property of BinomialHeap).
  override def insert(x: A, ts: H) = ins(Node(x, 0, Nil), ts)
  
  // Recursively ordering trees in heap by ascending rank
  override def meld(ts1: H, ts2: H) = (ts1, ts2) match {
    case (Nil, ts) => ts
    case (ts, Nil) => ts
    case (t1 :: ts1, t2 :: ts2) =>
      if (t1.r < t2.r) t1 :: meld(ts1, t2 :: ts2)
      else if (t2.r < t1.r) t2 :: meld(t1 :: ts1, ts2)
      else ins(link(t1, t2), meld(ts1, ts2)) // heads of both lists are of equal rank
  }

  // Recursive
  override def findMin(ts: H) = ts match {
    case Nil => throw new NoSuchElementException("min of empty heap")
    case t::Nil => root(t) // The name "root" seems to be making the assumption that the root has been found, and although this calling logic is consistant with that condition, root does not actually perform any logic of any type, and cannot verify or guarantee that it knows the value of the root.
    case t::ts => {
      /* This is basically recursively chaining through every sequential pair of nodes in 
       * in the list and comparing them. */
      val x = findMin(ts) // recursion
      if (ord.lteq(root(t), x)) root(t) else x
    }
  }
  
  // Returns a heap resulting from deleting the minimum of ts (H)
  override def deleteMin(ts: H) = ts match {
    case Nil => throw new NoSuchElementException("delete min of empty heap")
    case t::ts => {
      /* Recursive.  */
      def getMin(t: Node, ts: H): (Node, H) = ts match {
        case Nil => (t, Nil) // Convergence condition, recursion complete.
        case tp::tsp => {
          /* Very similar to findMin: recursively compares all pairs in sequence*/
          val (tq, tsq) = getMin(tp, tsp) // recursion on tail
          // compare head to min of tail. Recursion causes comparison to progress from the last of list to the the first of list.
          if (ord.lteq(root(t), root(tq))) (t,ts) else (tq, t::tsq)
        }
      }
      val (Node(_,_,c), tsq) = getMin(t, ts) // getMin recurses list
      meld(c.reverse, tsq) // Reorder BinomialQueue.nodes using list with min Node removed and min Node's children.
    } // end case t::ts
  }
}

/////////////// Bogus traits /////////////////

// Bug is that root is always returned as min. No recursive comparison takes place.
trait Bogus1BinomialHeap extends BinomialHeap {
  override def findMin(ts: H) = ts match {
    case Nil => throw new NoSuchElementException("min of empty heap")
    case t::ts => root(t)
  }
}

// Bug is that the lteq condition has been reversed so that min will not be at root.
trait Bogus2BinomialHeap extends BinomialHeap {
  override protected def link(t1: Node, t2: Node): Node = // t1.r==t2.r
    if (!ord.lteq(t1.x, t2.x)) Node(t1.x, t1.r+1, t2::t1.c) else Node(t2.x, t2.r+1, t1::t2.c)
}

// Bug is that the wrong node is being added to children
trait Bogus3BinomialHeap extends BinomialHeap {
  override protected def link(t1: Node, t2: Node): Node = // t1.r==t2.r
    if (ord.lteq(t1.x, t2.x)) Node(t1.x, t1.r+1, t1::t1.c) else Node(t2.x, t2.r+1, t2::t2.c)
}

// Bug is that min has not been found (findMin) and the head is assumed to be min.
trait Bogus4BinomialHeap extends BinomialHeap {
  override def deleteMin(ts: H) = ts match {
    case Nil => throw new NoSuchElementException("delete min of empty heap")
    case t::ts => meld(t.c.reverse, ts)
  }
}

/* Bug is that only one list is even being looked at and then it's arbitrarily 
 * making the head of ts1 the root and making all other nodes in both params its children. */
trait Bogus5BinomialHeap extends BinomialHeap {
  override def meld(ts1: H, ts2: H) = ts1 match {
    case Nil => ts2
    case t1::ts1 => List(Node(t1.x, t1.r, ts1 ++ ts2))
  }
}
