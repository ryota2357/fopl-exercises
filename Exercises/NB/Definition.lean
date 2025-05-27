namespace NB

/-
t ::= v
    | if t₁ then t₂ else t₃
    | succ(t) | pred(t) | iszero(t)
v ::= b | n
b ::= true | false
n ::= 0 | succ(n)
-/

inductive NatValue where
| zero : NatValue
| succ : NatValue → NatValue

inductive BoolValue where
| true : BoolValue
| false : BoolValue

inductive Value where
| bool : BoolValue → Value
| nat : NatValue → Value

inductive Term where
| value : Value → Term
| if_ : Term → Term → Term → Term
| succ : Term → Term
| pred : Term → Term
| iszero : Term → Term

open Term
open BoolValue
open NatValue

private abbrev t_true : Term := value (Value.bool true)
private abbrev t_false : Term := value (Value.bool false)
private abbrev t_zero : Term := value (Value.nat zero)
private abbrev t_nat (n : NatValue) : Term := value (Value.nat n)

inductive Step : Term → Term → Prop where
| eval_if_true : ∀ t₂ t₃, Step (if_ t_true t₂ t₃) t₂
| eval_if_false : ∀ t₂ t₃, Step (if_ t_false t₂ t₃) t₃
| eval_if : ∀ t₁ t₁' t₂ t₃, Step t₁ t₁' → Step (if_ t₁ t₂ t₃) (if_ t₁' t₂ t₃)
| eval_succ : ∀ t t', Step t t' → Step (succ t) (succ t')
| eval_pred : ∀ t t', Step t t' → Step (pred t) (pred t')
| eval_iszero : ∀ t t', Step t t' → Step (iszero t) (iszero t')
| eval_iszero_zero : Step (iszero t_zero) t_true
| eval_iszero_succ : ∀ n, Step (iszero (t_nat (succ n))) t_false
| eval_pred_zero : Step (pred t_zero) t_zero
| eval_pred_succ : ∀ n, Step (pred (t_nat (succ n))) (t_nat n)

infixl:50 " ⟶ " => Step

inductive MultiStep : Term → Term → Prop where
| refl : ∀ t, MultiStep t t
| step : ∀ t₁ t₂ t₃, Step t₁ t₂ → MultiStep t₂ t₃ → MultiStep t₁ t₃

infixl:50 " ⟶* " => MultiStep
