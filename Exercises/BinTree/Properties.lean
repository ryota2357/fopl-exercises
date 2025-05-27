import Exercises.BinTree.Definition

namespace BinTree

theorem size_leaf : size leaf = 1 := rfl

theorem size_branch (t₁ t₂ : BinTree) : (branch t₁ t₂).size = t₁.size + t₂.size + 1 := rfl

theorem height_leaf : height leaf = 0 := rfl

theorem height_branch (t₁ t₂ : BinTree) : (branch t₁ t₂).height = (max t₁.height t₂.height) + 1 := rfl

example : size (branch leaf (branch leaf leaf)) = 5 := by
  repeat rw [size_branch]
  rw [size_leaf]

example (t : BinTree) : size t > 0 := by
  induction t with
  | leaf =>
    rw [size_leaf]
    exact Nat.zero_lt_one
  | branch l r hl hr =>
    rw [size_branch]
    apply Nat.lt_add_right
    apply Nat.lt_trans hl
    apply Nat.lt_add_of_pos_right
    exact hr

example (t : BinTree) : size t > height t := by
  induction t with
  | leaf =>
    rw [size_leaf, height_leaf]
    exact Nat.zero_lt_one
  | branch l r hl hr =>
    rw [size_branch, height_branch]
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
