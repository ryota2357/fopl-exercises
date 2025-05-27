import Exercises.IfExpr.Definition

namespace IfExpr

namespace ex

open Term
def t₀ : Term := if_ true false true

/-
Step1:
                  ------------ (eval_if_true)
                   t₀ → false
      -------------------------------------------------- (eval_if)
       if t₀ then t₀ else t₀ → if false then t₀ else t₀

Step2:
      ---------------------------------- (eval_if_false)
       if false then t_0 else t_0 → t_0

Step3:
      ------------ (eval_if_true)
       t₀ → false
-/
example : if_ t₀ t₀ t₀ ⟶* false := by
  apply MultiStep.step
  · apply Step.eval_if
    exact Step.eval_if_true false true
  · apply MultiStep.step
    · exact Step.eval_if_false t₀ t₀
    · apply MultiStep.step
      · exact Step.eval_if_true false true
      · exact MultiStep.refl false

/-
  true ⇓ true (eval_value) false ⇓ false (eval_value)                 true ⇓ true (eval_value) false ⇓ false (eval_value)
 ---------------------------------------------------- (eval_if_true) ---------------------------------------------------- (eval_if_true)
                      t₀ ⇓ false                                                          t₀ ⇓ false
------------------------------------------------------------------------------------------------------------------------- (eval_if_false)
                                                      if t₀ then  t₀ else t₀ ⇓ false
-/
example : if_ t₀ t₀ t₀ ⇓ false := by
  apply BigStep.eval_if_false
  · apply BigStep.eval_if_true
    · exact BigStep.eval_value true
    · exact BigStep.eval_value false
  · apply BigStep.eval_if_true
    · exact BigStep.eval_value true
    · exact BigStep.eval_value false

end ex
