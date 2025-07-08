import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Use
import Exercises.STLC.Definition

namespace STLC

-- 変数の型付け関係 (Γ.lookup x = some τ → Γ ⊢ Term.var x ∷ τ) の逆
lemma typing_inversion_var : ∀ Γ x τ, (Γ ⊢ .var x ∷ τ) → Γ.lookup x = some τ := by
  intros Γ x τ h
  cases h with
  | var _ _ _ h_lookup =>
    exact h_lookup

-- λ抽象の型付け関係 ((Γ‚(x, τ₁) ⊢ t ∷ τ₂) → Γ ⊢ Term.lam x τ₁ t ∷ τ₁.func τ₂) の逆
lemma typing_inversion_abs : ∀ Γ x τ₁ t τ₂, (Γ ⊢ .lam x τ₁ t ∷ .func τ₁ τ₂) → (Γ‚(x, τ₁) ⊢ t ∷ τ₂) := by
  intros Γ x τ₁ t τ₂ h
  cases h with
  | abs _ _ _ _ _ h_body =>
    exact h_body

-- 関数適用の型付け関係 ((Γ ⊢ t₁ ∷ τ₁.func τ₂) → (Γ ⊢ t₂ ∷ τ₁) → Γ ⊢ t₁.app t₂ ∷ τ₂) の逆
lemma typing_inversion_app : ∀ Γ t₁ t₂ τ₂, (Γ ⊢ .app t₁ t₂ ∷ τ₂) → ∃ τ₁, (Γ ⊢ t₁ ∷ .func τ₁ τ₂) ∧ (Γ ⊢ t₂ ∷ τ₁) := by
  intros Γ t₁ t₂ τ₂ h
  cases h with
  | app _ _ _ τ_arg _ h₁ h₂  =>
    use τ_arg

theorem progress : ∀ t τ, ([] ⊢ t ∷ τ) → (Value t ∨ ∃ t', t ⟶ t') := by
  intros t τ h
  cases h with
  | var _ x τ' h_lookup =>
    left
    cases h_lookup
  | abs _ x τ₁ τ₂ t' h =>
    left
    exact Value.lam x τ₁ t'
  | app _ t₁ t₂ τ' _ h₁ h₂  =>
    right
    cases t₁ with
    | var x  =>
      exfalso
      cases h₁ with
      | var _ _ _ h_lookup  => cases h_lookup
    | app t₁' t₂' =>
      sorry
    | lam x τ_arg t_res =>
      use [x ↦ t₂]t_res
      exact Step.beta x τ_arg t_res t₂

theorem preservation : ∀ Γ t τ t', (Γ ⊢ t ∷ τ) ∧ (t ⟶ t') → (Γ ⊢ t' ∷ τ) := by
  intros Γ t τ t' h
  obtain ⟨hl, hr⟩ := h
  induction hl generalizing t' with
  | var Γ' x τ' h_lookup =>
    sorry
  | abs Γ' x τ₁ τ₂ t'' h_body ih =>
    sorry
  | app Γ' t₁ t₂ τ₁ τ₂ h₁ h₂ ih₁ ih₂ =>
    sorry

theorem preservation_on_subst : ∀ Γ x t t' τ τ', (Γ‚(x, τ') ⊢ t ∷ τ) ∧ (Γ ⊢ t' ∷ τ') → (Γ ⊢ [x ↦ t']t ∷ τ) := by
  intros Γ x t t' τ τ' h
  obtain ⟨hl, hr⟩ := h
  induction hr generalizing t with
  | var Γ' x' τ_x' h_lookup =>
    sorry
  | abs =>
    sorry
  | app =>
    sorry
