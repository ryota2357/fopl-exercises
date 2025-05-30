import Mathlib.Tactic.Lemma

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

inductive TermType where
| bool : TermType
| nat : TermType

inductive TypeJudgment : Term → TermType → Prop where
| bool_value : ∀ b, TypeJudgment (value (Value.bool b)) TermType.bool
| zero : TypeJudgment zero' TermType.nat
| succ : ∀ t, TypeJudgment t TermType.nat → TypeJudgment (succ t) TermType.nat
| pred : ∀ t, TypeJudgment t TermType.nat → TypeJudgment (pred t) TermType.nat
| iszero : ∀ t, TypeJudgment t TermType.nat → TypeJudgment (iszero t) TermType.bool
| if_ : ∀ t₁ t₂ t₃, ∀ τ,
    TypeJudgment t₁ TermType.bool → TypeJudgment t₂ τ → TypeJudgment t₃ τ →
    TypeJudgment (if_ t₁ t₂ t₃) τ

infixl:40 " ∷ " => TypeJudgment

/-
  このNBと型付け規則の問題: 次の補題が証明できない

    lemma nat_value_has_nat_type : ∀ n, (value (Value.nat n)) ∷ TermType.nat := by
      intro n
      induction n with
      | zero => exact TypeJudgment.zero
      | succ n' ih => sorry

  sorryの部分は:

    case succ
    n' : NatValue
    ih : value (Value.nat n') ∷ TermType.nat
    ⊢ value (Value.nat n'.succ) ∷ TermType.nat

  これに対して、次の(1)と(2)の方法などが思いつく。(2)を採用する。
-/

-- 方法(1): 型付け規則に入れてしまう。
-- inductive TypeJudgment : ... where
-- ...
-- | nat_value : ∀ n, TypeJudgment (value (Value.nat n)) TermType.nat

-- 方法(1)での証明
-- lemma nat_value_has_nat_type : ∀ n, (value (Value.nat n)) ∷ TermType.nat := by
--   exact fun n ↦ TypeJudgment.nat_value n

-- 方法(2): succ(n) は値としても項としても同じ形をしている。
axiom succ_term_nat_eq_term_succ_nat : ∀ n, (succ (value (Value.nat n))) = (value (Value.nat (NatValue.succ n)))

-- 方法(2)での証明
lemma nat_value_has_nat_type : ∀ n, (value (Value.nat n)) ∷ TermType.nat := by
  intro n
  induction n with
  | zero => exact TypeJudgment.zero
  | succ n' ih =>
    rw [← succ_term_nat_eq_term_succ_nat n']
    exact TypeJudgment.succ (value (Value.nat n')) ih
