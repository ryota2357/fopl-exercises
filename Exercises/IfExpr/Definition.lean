namespace IfExpr

inductive Term where
  | if_ : Term → Term → Term → Term
  | true : Term
  | false : Term

open Term

inductive Value : Term → Prop where
  | true : Value true
  | false : Value false

inductive Step : Term → Term → Prop where
  | eval_if_true : ∀ t₁ t₂, Step (if_ true t₁ t₂) t₁
  | eval_if_false : ∀ t₁ t₂, Step (if_ false t₁ t₂) t₂
  | eval_if : ∀ t₁ t₁' t₂ t₃, Step t₁ t₁' → Step (if_ t₁ t₂ t₃) (if_ t₁' t₂ t₃)

infixl:50 " ⟶ " => Step

inductive MultiStep : Term → Term → Prop where
  | refl : ∀ t, MultiStep t t
  | step : ∀ t₁ t₂ t₃, Step t₁ t₂ → MultiStep t₂ t₃ → MultiStep t₁ t₃

infixl:50 " ⟶* " => MultiStep

inductive BigStep : Term → Term → Prop where
  | eval_if_true : ∀ t₁ t₂ t₃ v, BigStep t₁ true → BigStep t₂ v → BigStep (if_ t₁ t₂ t₃) v
  | eval_if_false : ∀ t₁ t₂ t₃ v, BigStep t₁ false → BigStep t₃ v → BigStep (if_ t₁ t₂ t₃) v
  | eval_value : ∀ v, BigStep v v

infixl:50 " ⇓ " => BigStep
