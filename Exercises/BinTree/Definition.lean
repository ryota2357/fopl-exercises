inductive BinTree where
| Branch : BinTree → BinTree → BinTree
| Leaf   : BinTree

namespace BinTree

-- l.Branch r を Branch l r と表示する
-- @[app_unexpander BinTree]
-- def unexpandBranch : Lean.PrettyPrinter.Unexpander
--   | `($l $r) => `(`Branch $l $r)
--   | _ => throw ()

def size (t : BinTree) : Nat :=
  match t with
  | Branch l r => l.size + r.size + 1
  | Leaf       => 1

def height (t : BinTree) : Nat :=
  match t with
  | Branch l r => (max l.height r.height) + 1
  | Leaf       => 0
