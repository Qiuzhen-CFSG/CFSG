module

public import Theory.SpecificGroups.G2.MultiplierThree.Reduction
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.Construction

/-!
# Assembling a cubic extension from the ATLAS projective relations

Pair an evaluation of the six source words with their presented quotient.
The paired image has central kernel; the corrected last relator is in its
derived subgroup. A matrix evaluation of order three therefore gives the
lower bound on the literal universal kernel, once the presented quotient
has been identified with the actual split-octonion automorphism group.

The matrix certificate and that isomorphism remain explicit inputs here.
The numerical candidates are in `CubicExtension.MatrixData`; no group label
or external computation is used as a proof. In particular this module does
not yet assert the unconditional lower bound.

Source: Aschbacher–Smith I.1.4(2), printed p.408 (PDF p.419), GLS3 §6.1,
and the ATLAS six-relator presentation cited in `CubicExtension.Presentation`.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension
open Presentation

universe u
variable {H : Type u} [Group H]

/-- The extension projection to the literal octonion model, after comparison. -/
def modelProjection (e : Presented ≃* Model (ZMod 3)) (f : Free →* H) :
    Extension f →* Model (ZMod 3) := e.toMonoidHom.comp (projection f)

theorem modelProjection_surjective (e : Presented ≃* Model (ZMod 3))
    (f : Free →* H) : Function.Surjective (modelProjection e f) :=
  e.surjective.comp (projection_surjective f)

theorem modelProjection_ker_le_center (e : Presented ≃* Model (ZMod 3))
    (f : Free →* H) (hc : ∀ i, f (relator i) ∈ Subgroup.center H) :
    (modelProjection e f).ker ≤ Subgroup.center (Extension f) := by
  intro x hx
  apply projection_ker_le_center f hc
  exact e.injective (hx.trans e.map_one.symm)

/-- The paired-image construction supplies an actual central derived element;
only the independent presentation comparison and evaluation remain as inputs. -/
theorem three_dvd_kernel_card_of_evaluation
    (e : Presented ≃* Model (ZMod 3)) (f : Free →* H)
    (hc : ∀ i, f (relator i) ∈ Subgroup.center H)
    (ho : orderOf (f defect) = 3) : 3 ∣ Nat.card (Kernel (ZMod 3)) := by
  apply three_dvd_kernel_card_of_central_extension (modelProjection e f)
    (modelProjection_surjective e f) (modelProjection_ker_le_center e f hc)
    (liftedDefect f) ?_ (liftedDefect_mem_commutator f) ?_
  · change e (toPresented defect) = 1
    rw [toPresented_defect, e.map_one]
  · rw [orderOf_liftedDefect, ho]

/-- A projective pair with trivial first three relators and a cubic last
relator yields the required lower bound after identifying the presented base. -/
theorem three_dvd_kernel_card_of_projective_pair
    (e : Presented ≃* Model (ZMod 3)) (a b : H)
    (hc : ∀ i, word a b i ∈ Subgroup.center H)
    (h0 : word a b 0 = 1) (h1 : word a b 1 = 1) (h2 : word a b 2 = 1)
    (ho : orderOf (word a b 5) = 3) : 3 ∣ Nat.card (Kernel (ZMod 3)) := by
  let f : Free →* H := FreeGroup.lift (fun x => if x then b else a)
  have hf (i : Fin 6) : f (relator i) = word a b i := by
    simp only [f, relator, map_word, FreeGroup.lift_apply_of, Bool.false_eq_true,
      reduceIte]
  apply three_dvd_kernel_card_of_evaluation e f
  · intro i
    rw [hf]
    exact hc i
  · have hd : f defect = defectWord a b := by
      simp only [defect, f, map_defectWord, FreeGroup.lift_apply_of,
        Bool.false_eq_true, reduceIte]
    rw [hd, defectWord_eq_last a b h0 h1 h2]
    exact ho

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension
