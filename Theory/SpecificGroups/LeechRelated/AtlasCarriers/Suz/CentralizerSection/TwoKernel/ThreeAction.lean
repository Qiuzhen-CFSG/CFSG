module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.BlockAction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.TwoKernel.ThreeCertificates

import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.Action
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.BlockAction

/-!
# Checked commuting cubic words in the fixed Suz centralizer

The three displayed words belong to `numerator = ⟨c,d⟩`. The numerical
certificates prove their cubes and pairwise commutators are trivial by
faithfulness of the original degree-1782 permutation representation.
The internal imports reuse the existing evaluation helpers and unfold the
marked numerator generators only inside these proofs.
Source: the retained ATLAS permutations; Aschbacher--Smith A.2.19 and I.1.3.
-/

public section
namespace Sporadic.LeechRelated.Suz.CentralizerSection.ThreeWitness
set_option maxRecDepth 2048
set_option Elab.async false
open Tables

/-- The original permutation representation restricted to the centralizing words. -/
def representation : numerator →* Equiv.Perm (Fin 1782) :=
  inclusion.comp numerator.subtype

theorem representation_injective : Function.Injective representation :=
  inclusion_injective.comp Subtype.val_injective

/-- The first cubic word. -/
@[irreducible] def x : numerator := dInNumerator ^ 4
/-- Conjugating word for the second cubic generator. -/
@[irreducible] def hWord : numerator :=
  cInNumerator⁻¹ * dInNumerator * cInNumerator * dInNumerator * cInNumerator ^ 2
/-- Conjugating word for the third cubic generator. -/
@[irreducible] def kWord : numerator := cInNumerator * dInNumerator ^ 3 * cInNumerator⁻¹
/-- The second cubic word. -/
@[irreducible] def y : numerator := hWord * x * hWord⁻¹
/-- The third cubic word. -/
@[irreducible] def t : numerator := kWord * x * kWord⁻¹

private theorem c_eval (a : Fin 1782) : representation cInNumerator a = cMap a :=
  c_apply a
private theorem d_eval (a : Fin 1782) : representation dInNumerator a = dMap a :=
  d_apply a
private theorem ci_eval (a : Fin 1782) : representation cInNumerator⁻¹ a = ciMap a :=
  eval_inv representation c_eval (fun b => (pointFacts b).1) a

private theorem h_eval (a : Fin 1782) : representation hWord a = hMap a := by
  unfold hWord
  exact (eval_mul representation (eval_mul representation (eval_mul representation
    (eval_mul representation ci_eval d_eval) c_eval) d_eval)
    (eval_pow representation c_eval 2) a).trans (pointFacts a).2.1.symm

private theorem k_eval (a : Fin 1782) : representation kWord a = kMap a := by
  unfold kWord
  exact (eval_mul representation (eval_mul representation c_eval
    (eval_pow representation d_eval 3)) ci_eval a).trans (pointFacts a).2.2.1.symm

private theorem hi_eval (a : Fin 1782) : representation hWord⁻¹ a = hiMap a :=
  eval_inv representation h_eval (fun b => (pointFacts b).2.2.2.1) a
private theorem ki_eval (a : Fin 1782) : representation kWord⁻¹ a = kiMap a :=
  eval_inv representation k_eval (fun b => (pointFacts b).2.2.2.2.1) a

theorem x_apply (a : Fin 1782) : representation x a = xMap a := by
  unfold x
  exact (eval_pow representation d_eval 4 a).trans (pointFacts a).2.2.2.2.2.1.symm

theorem y_apply (a : Fin 1782) : representation y a = yMap a := by
  unfold y
  exact (eval_mul representation (eval_mul representation h_eval x_apply) hi_eval a).trans
    (pointFacts a).2.2.2.2.2.2.1.symm

theorem t_apply (a : Fin 1782) : representation t a = tMap a := by
  unfold t
  exact (eval_mul representation (eval_mul representation k_eval x_apply) ki_eval a).trans
    (pointFacts a).2.2.2.2.2.2.2.1.symm

private theorem cube_of_eval {g : numerator} {A : Fin 1782 → Fin 1782}
    (ha : ∀ a, representation g a = A a) (hc : ∀ a, A (A (A a)) = a) :
    g ^ 3 = 1 := by
  apply representation_injective
  apply Equiv.ext
  intro a
  simpa only [map_one, Equiv.Perm.one_apply] using
    (eval_pow representation ha 3 a).trans (hc a)

theorem x_cube : x ^ 3 = 1 :=
  cube_of_eval x_apply (fun a => (pointFacts a).2.2.2.2.2.2.2.2.1)
theorem y_cube : y ^ 3 = 1 :=
  cube_of_eval y_apply (fun a => (pointFacts a).2.2.2.2.2.2.2.2.2.1)
theorem t_cube : t ^ 3 = 1 :=
  cube_of_eval t_apply (fun a => (pointFacts a).2.2.2.2.2.2.2.2.2.2.1)

private theorem commute_of_eval {g h : numerator} {A B : Fin 1782 → Fin 1782}
    (ha : ∀ a, representation g a = A a) (hb : ∀ a, representation h a = B a)
    (hc : ∀ a, A (B a) = B (A a)) : Commute g h := by
  apply representation_injective
  apply Equiv.ext
  intro a
  exact (eval_mul representation ha hb a).trans ((hc a).trans
    (eval_mul representation hb ha a).symm)

theorem x_commute_y : Commute x y :=
  commute_of_eval x_apply y_apply (fun a => (pointFacts a).2.2.2.2.2.2.2.2.2.2.2.1)
theorem x_commute_t : Commute x t :=
  commute_of_eval x_apply t_apply (fun a => (pointFacts a).2.2.2.2.2.2.2.2.2.2.2.2.1)
theorem y_commute_t : Commute y t :=
  commute_of_eval y_apply t_apply (fun a => (pointFacts a).2.2.2.2.2.2.2.2.2.2.2.2.2)

end Sporadic.LeechRelated.Suz.CentralizerSection.ThreeWitness
