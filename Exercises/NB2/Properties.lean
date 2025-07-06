import Mathlib.Tactic.Use
import Exercises.NB2.Definition

namespace NB2

/-
  NB の停止性の証明
  - Termination measure として 項のサイズ `termSize` を用いる
  - 任意の遷移 `t ⟶ t'` に対して `termSize t > termSize t'` が成り立つことを示す (`term_size_step`)
-/

def termSize (t : Term) : Nat :=
  match t with
  | .true  => 1
  | .false => 1
  | .zero  => 1
  | .succ t' => 1 + termSize t'
  | .pred t' => 1 + termSize t'
  | .iszero t' => 1 + termSize t'
  | .if_ t₁ t₂ t₃ => 1 + termSize t₁ + termSize t₂ + termSize t₃

theorem term_size_step : ∀ t t', t ⟶ t' → termSize t > termSize t' := by
  intros t t' h
  -- NBの方で丁寧にNatで証明したので、ここでは omega で省略する
  induction h <;> simp only [termSize] <;> omega

/-
  NB の型システムの健全性 (= 進行 + 保存) の証明
  - 進行 (progress) : 型がついたら stuck しない
      t : τ ならば、t は値か、t ⟶ t' となる t' が存在する
  - 保存 (preservation) : 評価の進行で型が変わらない
      t : τ かつ t ⟶ t' ならば t' : τ が成り立つ
-/

theorem type_progress : ∀ t τ, t ∷ τ → (Value t) ∨ (∃ t', t ⟶ t') := by
  intros t τ h
  induction h with
  | bool b h =>
    left
    cases b with
    | true => exact Value.true
    | false => exact Value.false
    | _ =>
      exfalso
      cases h
  | zero =>
    left
    exact Value.zero
  | succ t' ht ih =>
    cases ih with
    | inl h =>
      left
      cases t' with
      | zero =>
        apply Value.succ Term.zero
        exact h
      | succ n =>
        apply Value.succ n.succ
        exact h
      | pred n =>
        apply Value.succ n.pred
        exact h
      | if_ t₁ t₂ t₃ =>
        apply Value.succ (t₁.if_ t₂ t₃)
        exact h
      | true | false | iszero =>
        exfalso
        cases ht
    | inr h =>
      right
      obtain ⟨t'', h'⟩ := h
      use Term.succ t''
      exact Step.eval_succ t' t'' h'
  | pred t' ht ih =>
    right
    cases ih with
    | inl h =>
      cases t' with
      | zero =>
        use Term.zero
        exact Step.eval_pred_zero
      | succ n =>
        use n
        exact Step.eval_pred_succ n
      | pred n =>
        exfalso
        cases h
      | if_ t₁ t₂ t₃ =>
        exfalso
        cases h
      | true | false | iszero =>
        exfalso
        cases ht
    | inr h =>
      obtain ⟨t'', h'⟩ := h
      use Term.pred t''
      exact Step.eval_pred t' t'' h'
  | iszero t' ht ih =>
    right
    cases ih with
    | inl h =>
      cases t' with
      | zero =>
        use Term.true
        exact Step.eval_iszero_zero
      | succ n =>
        use Term.false
        exact Step.eval_iszero_succ n
      | pred n =>
        exfalso
        cases h
      | if_ t₁ t₂ t₃ =>
        exfalso
        cases h
      | true | false | iszero =>
        exfalso
        cases ht
    | inr h =>
      obtain ⟨t'', h'⟩ := h
      use Term.iszero t''
      exact Step.eval_iszero t' t'' h'
  | if_ t₁ t₂ t₃ τ' ht₁ ht₂ ht₃ ih₁ ih₂ ih₃ =>
    right
    cases ih₁ with
    | inl h =>
      cases t₁ with
      | zero | succ | pred =>
        exfalso
        cases ht₁
        rename_i h'
        cases h'
      | true =>
        use t₂
        exact Step.eval_if_true t₂ t₃
      | false =>
        use t₃
        exact Step.eval_if_false t₂ t₃
      | iszero n =>
        exfalso
        cases h
      | if_ t₁ t₂ t₃ =>
        exfalso
        cases h
    | inr h =>
      obtain ⟨t₁', h'⟩ := h
      use Term.if_ t₁' t₂ t₃
      exact Step.eval_if t₁ t₁' t₂ t₃ h'

theorem type_preservation : ∀ t t' τ, t ∷ τ ∧ t ⟶ t' → t' ∷ τ := by
  intros t t' τ h
  obtain ⟨hl, hr⟩ := h
  induction hl generalizing t' with
  | bool b h =>
    exfalso
    cases hr <;> cases h -- 矛盾
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
    | eval_pred_succ n =>
      cases ht₁ with
      | succ _ hn => exact hn
    | eval_pred _ t₁' h₁ =>
      apply TypeJudgment.pred
      apply ih
      exact h₁
  | iszero t₁ ht₁ ih =>
    cases hr with
    | eval_iszero_zero =>
      apply TypeJudgment.bool Term.true
      rfl
    | eval_iszero_succ n =>
      apply TypeJudgment.bool Term.false
      rfl
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
