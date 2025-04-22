import Exercises.BinTree

namespace BinTree

theorem leaf_size_one : size Leaf = 1 := rfl

theorem branch_size_sum (t1 t2 : BinTree) : (Branch t1 t2).size = t1.size + t2.size + 1 := rfl

theorem leaf_height_zero : height Leaf = 0 := rfl

theorem branch_height_sum (t1 t2 : BinTree) : (Branch t1 t2).height = (max t1.height t2.height) + 1 := rfl

example : size (Branch Leaf (Branch Leaf Leaf)) = 5 := by
  repeat rw [branch_size_sum]
  rw [leaf_size_one]

example (t : BinTree) : size t > 0 := by
  induction t with
  | Leaf =>
    rw [leaf_size_one]
    exact Nat.zero_lt_one
  | Branch l r hl hr =>
    rw [branch_size_sum]
    apply Nat.lt_add_right
    apply Nat.lt_trans hl
    apply Nat.lt_add_of_pos_right
    exact hr

example (t : BinTree) : size t > height t := by
  induction t with
  | Leaf =>
    rw [leaf_size_one, leaf_height_zero]
    exact Nat.zero_lt_one
  | Branch l r hl hr =>
    rw [branch_size_sum, branch_height_sum]
    apply Nat.add_lt_add_right
    cases Nat.le_total l.height r.height with
    | inl h =>
      rw [Nat.max_eq_right h]
      rw [Nat.add_comm]
      apply Nat.le_add_right_of_le
      apply Nat.succ_le.mpr
      exact hr
    | inr h =>
      rw [Nat.max_eq_left h]
      apply Nat.le_add_right_of_le
      apply Nat.succ_le.mpr
      exact hl
