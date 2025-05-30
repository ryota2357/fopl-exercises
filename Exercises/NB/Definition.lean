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

private abbrev true' : Term := value (Value.bool BoolValue.true)
private abbrev false' : Term := value (Value.bool BoolValue.false)
private abbrev zero' : Term := value (Value.nat NatValue.zero)
private abbrev succ' (n : NatValue) : Term := value (Value.nat (NatValue.succ n))

inductive Step : Term → Term → Prop where
| eval_if_true : ∀ t₂ t₃, Step (if_ true' t₂ t₃) t₂
| eval_if_false : ∀ t₂ t₃, Step (if_ false' t₂ t₃) t₃
| eval_if : ∀ t₁ t₁' t₂ t₃, Step t₁ t₁' → Step (if_ t₁ t₂ t₃) (if_ t₁' t₂ t₃)
| eval_succ : ∀ t t', Step t t' → Step (succ t) (succ t')
| eval_pred : ∀ t t', Step t t' → Step (pred t) (pred t')
| eval_iszero : ∀ t t', Step t t' → Step (iszero t) (iszero t')
| eval_iszero_zero : Step (iszero zero') true'
| eval_iszero_succ : ∀ n, Step (iszero (succ' n)) false'
| eval_pred_zero : Step (pred zero') zero'
| eval_pred_succ : ∀ n, Step (pred (succ' n)) (value (Value.nat n))

infixl:50 " ⟶ " => Step

inductive MultiStep : Term → Term → Prop where
| refl : ∀ t, MultiStep t t
| step : ∀ t₁ t₂ t₃, Step t₁ t₂ → MultiStep t₂ t₃ → MultiStep t₁ t₃

infixl:50 " ⟶* " => MultiStep
