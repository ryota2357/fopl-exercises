namespace NB2

/-
  t ::= v
      | if t₁ then t₂ else t₃
      | succ(t) | pred(t) | iszero(t)
  v ::= b | n
  b ::= true | false
  n ::= 0 | succ(n)
-/

inductive Term where
| true
| false
| zero
| succ : Term → Term
| if_ : Term → Term → Term → Term
| pred : Term → Term
| iszero : Term → Term

inductive Value : Term → Prop where
| true : Value .true
| false : Value .false
| zero : Value .zero
| succ : ∀ n, Value n → Value (.succ n)

def isBoolValue : Term → Bool
| .true | .false => true
| _              => false

def isNumValue : Term → Bool
| .zero   => true
| .succ n => isNumValue n
| _       => false

open Term

inductive Step : Term → Term → Prop where
| eval_if_true : ∀ t₂ t₃, Step (if_ true t₂ t₃) t₂
| eval_if_false : ∀ t₂ t₃, Step (if_ false t₂ t₃) t₃
| eval_if : ∀ t₁ t₁' t₂ t₃, Step t₁ t₁' → Step (if_ t₁ t₂ t₃) (if_ t₁' t₂ t₃)
| eval_succ : ∀ t t', Step t t' → Step (succ t) (succ t')
| eval_pred : ∀ t t', Step t t' → Step (pred t) (pred t')
| eval_iszero : ∀ t t', Step t t' → Step (iszero t) (iszero t')
| eval_iszero_zero : Step (iszero zero) true
| eval_iszero_succ : ∀ n, Step (iszero (succ n)) false
| eval_pred_zero : Step (pred zero) zero
| eval_pred_succ : ∀ n, Step (pred (succ n)) n

infixl:50 " ⟶ " => Step

inductive MultiStep : Term → Term → Prop where
| refl : ∀ t, MultiStep t t
| step : ∀ t₁ t₂ t₃, Step t₁ t₂ → MultiStep t₂ t₃ → MultiStep t₁ t₃

infixl:50 " ⟶* " => MultiStep

inductive TermType where
| bool : TermType
| nat : TermType

inductive TypeJudgment : Term → TermType → Prop where
| bool : ∀ b, isBoolValue b → TypeJudgment b .bool
| zero : TypeJudgment zero .nat
| succ : ∀ t, TypeJudgment t .nat → TypeJudgment (succ t) .nat
| pred : ∀ t, TypeJudgment t .nat → TypeJudgment (pred t) .nat
| iszero : ∀ t, TypeJudgment t .nat → TypeJudgment (iszero t) .bool
| if_ : ∀ t₁ t₂ t₃, ∀ τ,
    TypeJudgment t₁ .bool → TypeJudgment t₂ τ → TypeJudgment t₃ τ →
    TypeJudgment (if_ t₁ t₂ t₃) τ

infixl:40 " ∷ " => TypeJudgment
