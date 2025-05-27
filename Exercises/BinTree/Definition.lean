inductive BinTree where
| branch : BinTree → BinTree → BinTree
| leaf

namespace BinTree

def size (t : BinTree) : Nat :=
  match t with
  | branch l r => l.size + r.size + 1
  | leaf       => 1

def height (t : BinTree) : Nat :=
  match t with
  | branch l r => (max l.height r.height) + 1
  | leaf       => 0
