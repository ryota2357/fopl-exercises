import Mathlib.Tactic.Lemma

namespace STLC

/-
  t ::= x            {変数}
      | λx:τ.t₁      {λ抽象}
      | t₁ t₂        {適用}
  v ::= λx:τ.t₁      {値}
  r ::= (λx:τ.t₁) v₂ {redex}
  τ ::= τ₁ → τ₂      {関数型}
      | A            {基底型}
  Γ ::= ∅            {空の型環境}
      | Γ,x:τ        {束縛がある型環境}
-/

structure Var where
  id : Nat
  deriving DecidableEq, Repr

inductive TermType : Type where
| base : String → TermType
| func : TermType → TermType → TermType
deriving DecidableEq, Repr

inductive Term where
| var : Var → Term
| lam : Var → TermType → Term → Term
| app : Term → Term → Term

inductive Value : Term → Prop where
| lam : ∀ x τ t , Value (Term.lam x τ t)

def TypeEnv := List (Var × TermType)

def TypeEnv.lookup (Γ : TypeEnv) (x : Var) : Option TermType :=
  match Γ with
  | [] => none
  | (y, τ) :: Γ' => if x = y then some τ else lookup Γ' x

abbrev TypeEnv.snoc (Γ : TypeEnv) (x : Var × TermType) : TypeEnv := x :: Γ

infixl:50 "‚" => TypeEnv.snoc

inductive TermTyping : TypeEnv → Term → TermType → Prop where
| var : ∀ Γ x τ, Γ.lookup x = some τ → TermTyping Γ (.var x) τ
| abs : ∀ Γ x τ₁ τ₂ t, TermTyping (Γ‚(x, τ₁)) t τ₂ → TermTyping Γ (.lam x τ₁ t) (.func τ₁ τ₂)
| app : ∀ Γ t₁ t₂ τ₁ τ₂,
  TermTyping Γ t₁ (.func τ₁ τ₂) → TermTyping Γ t₂ τ₁ →
  TermTyping Γ (.app t₁ t₂) τ₂

notation:40 Γ " ⊢ " t " ∷ " τ => TermTyping Γ t τ

def subst (t : Term) (x : Var) (v : Term) : Term :=
  match t with
  | .var y => if x = y then t else Term.var y
  | .lam y τ t' =>
    if x = y then Term.lam y τ t'
    else Term.lam y τ (subst t' x v)
  | .app t₁ t₂ => Term.app (subst t₁ x v) (subst t₂ x v)

notation:90 " [" x " ↦ " v "]" t => subst t x v

inductive Step : Term → Term → Prop where
  | beta : ∀ x τ t v, Step (.app (.lam x τ t) v) ([x ↦ v]t)
  | app1 : ∀ t₁ t₁' t₂, Step t₁ t₁' → Step (.app t₁ t₂) (.app t₁' t₂)
  | app2 : ∀ v₁ t₂ t₂', Step t₂ t₂' → Step (.app v₁ t₂) (.app v₁ t₂')

notation:50 t₁ " ⟶ " t₂ => Step t₁ t₂

inductive Steps : Term → Term → Prop where
  | refl : ∀ t , Steps t t
  | step : ∀ t₁ t₂ t₃, Step t₁ t₂ → Steps t₂ t₃ → Steps t₁ t₃

notation:50 t₁ " ⟶* " t₂ => Steps t₁ t₂

lemma type_uniqueness : ∀ Γ t τ₁ τ₂, (Γ ⊢ t ∷ τ₁) → (Γ ⊢ t ∷ τ₂) → (τ₁ = τ₂) := by
  intros Γ t τ₁ τ₂ h₁ h₂
  induction h₁ generalizing τ₂ with
  | var Γ' x τ h_lookup₁ =>
    cases h₂ with
    | var _ _ _ h_lookup₂ =>
      rw [h_lookup₁] at h_lookup₂
      injection h_lookup₂
  | abs Γ' x τ_arg₁ τ_res₁ t₁' h_body₁ ih =>
    cases h₂ with
    | abs _ _ τ_arg₂ τ_res₂ _ h_body₂ =>
      have τ_res_eq := ih τ_res₂ h_body₂
      rw [τ_res_eq]
  | app Γ' t₁' t₂' τ_arg₁ τ_res₁ h₁₁ h₁₂ ih₁ ih₂  =>
    cases h₂ with
    | app _ _ _ τ_arg₂ τ_res₂ h₂₁ h₂₂ =>
      have h_eq := ih₁ (TermType.func τ_arg₂ τ₂) h₂₁
      injection h_eq
