import Exercises.NB.Definition

namespace NB

/-
  NB の停止性の証明
  - Termination measure として 項のサイズ `termSize` を用いる
  - 任意の遷移 `t ⟶ t'` に対して `termSize t > termSize t'` が成り立つことを示す (`term_size_step`)
-/

def termSize (t : Term) : Nat :=
  match t with
  | Term.value _      => 1
  | Term.if_ t₁ t₂ t₃ => 1 + termSize t₁ + termSize t₂ + termSize t₃
  | Term.succ t       => 1 + termSize t
  | Term.pred t       => 1 + termSize t
  | Term.iszero t     => 1 + termSize t

theorem term_size_step : ∀ t t', t ⟶ t' → termSize t > termSize t' := by
  intros t t' h
  induction h with
  | eval_if_true t₂ t₃ =>
    simp only [termSize]
    apply Nat.lt_add_right (termSize t₃)
    apply Nat.lt_add_of_pos_left
    apply Nat.zero_lt_succ
  | eval_if_false t₂ t₃ =>
    simp only [termSize]
    apply Nat.lt_add_of_pos_left
    apply Nat.lt_add_right (termSize t₂)
    apply Nat.zero_lt_succ
  | eval_if t₁ t₁' t₂ t₃ _ ih =>
    simp only [termSize]
    repeat apply Nat.add_lt_add_iff_right.mpr
    apply Nat.add_lt_add_iff_left.mpr
    exact ih
  | eval_succ t t' _ ih =>
    simp only [termSize]
    apply Nat.add_lt_add_left
    exact ih
  | eval_pred t t' _ ih =>
    simp only [termSize]
    apply Nat.add_lt_add_left
    exact ih
  | eval_iszero t t' _ ih =>
    simp only [termSize]
    apply Nat.add_lt_add_left
    exact ih
  | eval_iszero_zero =>
    simp only [termSize]
    apply Nat.lt_add_one
  | eval_iszero_succ n =>
    simp only [termSize]
    apply Nat.lt_add_one
  | eval_pred_zero =>
    simp only [termSize]
    apply Nat.lt_add_one
  | eval_pred_succ n =>
    simp only [termSize]
    apply Nat.lt_add_one
