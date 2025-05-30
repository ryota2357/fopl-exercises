import Mathlib.Tactic.Use
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

/-
  NB の型システムの健全性 (= 進行 + 保存) の証明
  - 進行 (progress) : 型がついたら stuck しない
      t : τ ならば、t は値か、t ⟶ t' となる t' が存在する
  - 保存 (preservation) : 評価の進行で型が変わらない
      t : τ かつ t ⟶ t' ならば t' : τ が成り立つ
-/

theorem type_progress : ∀ t τ, t ∷ τ → (∃ v, t = Term.value v) ∨ (∃ t', t ⟶ t') := by
  intros t τ h
  induction h with
  | bool_value b =>
    left
    use Value.bool b
  | zero =>
    left
    use Value.nat NatValue.zero
  | succ t' ht ih =>
    cases ih with
    | inl h =>
      left
      obtain ⟨v, hv⟩ := h
      rw [hv] at ht
      cases v with
      | bool b => cases ht  -- 矛盾
      | nat n =>
        use Value.nat (NatValue.succ n)
        rw [hv]
        exact succ_term_nat_eq_term_succ_nat n
    | inr h =>
      right
      obtain ⟨t'', h'⟩ := h
      use Term.succ t''
      exact Step.eval_succ t' t'' h'
  | pred t' ht ih =>
    right
    cases ih with
    | inl h =>
      obtain ⟨v, hv⟩ := h
      rw [hv] at ht
      cases v with
      | bool b => cases ht  -- 矛盾
      | nat n =>
        rw [hv]
        cases n with
        | zero =>
          use Term.value (Value.nat NatValue.zero)
          exact Step.eval_pred_zero
        | succ n' =>
          use Term.value (Value.nat n')
          exact Step.eval_pred_succ n'
    | inr h =>
      obtain ⟨t'', h'⟩ := h
      use Term.pred t''
      exact Step.eval_pred t' t'' h'
  | iszero t ht ih =>
    right
    cases ih with
    | inl h =>
      obtain ⟨v, hv⟩ := h
      rw [hv] at ht
      cases v with
      | bool b => cases ht  -- 矛盾
      | nat n =>
        rw [hv]
        cases n with
        | zero =>
          use Term.value (Value.bool BoolValue.true)
          exact Step.eval_iszero_zero
        | succ n' =>
          use Term.value (Value.bool BoolValue.false)
          exact Step.eval_iszero_succ n'
    | inr h =>
      obtain ⟨t'', h'⟩ := h
      use Term.iszero t''
      exact Step.eval_iszero t t'' h'
  | if_ t₁ t₂ t₃ τ' ht₁ ht₂ ht₃ ih₁ ih₂ ih₃ =>
    right
    cases ih₁ with
    | inl h =>
      obtain ⟨v, hv⟩ := h
      rw [hv] at ht₁
      cases v with
      | nat n => cases ht₁  -- 矛盾
      | bool b =>
        rw [hv]
        cases b with
        | true =>
          use t₂
          exact Step.eval_if_true t₂ t₃
        | false =>
          use t₃
          exact Step.eval_if_false t₂ t₃
    | inr h =>
      obtain ⟨t₁', h'⟩ := h
      use Term.if_ t₁' t₂ t₃
      exact Step.eval_if t₁ t₁' t₂ t₃ h'

theorem type_preservation : ∀ t t' τ, t ∷ τ ∧ t ⟶ t' → t' ∷ τ := by
  intros t t' τ h
  obtain ⟨hl, hr⟩ := h
  induction hl generalizing t' with
  | bool_value b =>
    exfalso
    cases hr  -- 矛盾
  | zero =>
    exfalso
    cases hr  -- 矛盾
  | succ t₁ ht₁ ih =>
    cases hr with
    | eval_succ _ t₁' h₁ =>
      apply TypeJudgment.succ
      apply ih
      exact h₁
  | pred t₁ ht₁ ih =>
    cases hr with
    | eval_pred_zero => exact ht₁
    | eval_pred_succ n => exact nat_value_has_nat_type n
    | eval_pred _ t₁' h₁ =>
      apply TypeJudgment.pred
      apply ih
      exact h₁
  | iszero t₁ ht₁ ih =>
    cases hr with
    | eval_iszero_zero => exact TypeJudgment.bool_value BoolValue.true
    | eval_iszero_succ n => exact TypeJudgment.bool_value BoolValue.false
    | eval_iszero _ t₁' h₁ =>
      apply TypeJudgment.iszero
      apply ih
      exact h₁
  | if_ t₁ t₂ t₃ τ' ht₁ ht₂ ht₃ ih₁ ih₂ ih₃ =>
    cases hr with
    | eval_if_true => exact ht₂
    | eval_if_false => exact ht₃
    | eval_if _ t₁' _ _ ht₁' =>
      apply TypeJudgment.if_
      . apply ih₁
        exact ht₁'
      . exact ht₂
      . exact ht₃
