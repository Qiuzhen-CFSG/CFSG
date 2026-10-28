module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Inner
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Covers
public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.SourceBound

/-!
# The literal SL₃ cover and completed cubic model sieve

Faithfulness on the irreducible binary component makes its center odd. The
ordinary scalar-cover lift and the proved exceptional calculations at field
orders two and four therefore construct a surjection from SL₃ over the given
matrix field, commuting with the original projective marking.

The full automorphism-rank bound and both actor estimates then discharge
every premise of the original cubic model sieve. Its natural and half-field
tensor alternatives retain their actual inflated actions and intertwiners.

Source: Aschbacher–Smith I.1.3 and K.3.2, printed pp.407 and 454–456.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open PerfectCentralCovering
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.SourceFF
open ChapterB.QuasisimpleSource ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V]
  [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
  {K : GroupClass.{u}} {L : Subgroup G}

/-- Construct the actual scalar covering over the prescribed quotient map,
including both exceptional small fields. -/
theorem exists_linearCover (h : SourceHypothesis K ρ L) (B : BinaryField)
    (e : L ⧸ center L ≃* PSL(3,B.Carrier)) :
    ∃ C : LinearCover B 3 L,
      (e.toMonoidHom.comp (QuotientGroup.mk' (center L))).comp C.projection =
        Matrix.PSL3.projection B.Carrier := by
  let := h.finite_group
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  have ho := Alternating.component_center_odd ρ L h.faithful h.irreducible
  have hmap : ∃ k : SL(3,B.Carrier) →* L, Function.Surjective k ∧
      (centralQuotientCover e).toMonoidHom.comp k = Matrix.PSL3.projection B.Carrier := by
    by_cases h2 : Nat.card B.Carrier = 2
    · have hz := Matrix.PSL3.BinaryOddCenterCover.center_eq_bot_two h2 e ho
      let f := (centralQuotientCover e).toMonoidHom
      have hf : Function.Injective f := by
        apply (MonoidHom.ker_eq_bot_iff f).mp
        exact (centralQuotientCover_ker e).trans hz
      let j : L ≃* PSL(3,B.Carrier) :=
        MulEquiv.ofBijective f ⟨hf, (centralQuotientCover e).surjective⟩
      refine ⟨j.symm.toMonoidHom.comp (Matrix.PSL3.projection B.Carrier),
        j.symm.surjective.comp (Matrix.PSL3.projection_surjective B.Carrier), ?_⟩
      ext x
      exact j.apply_symm_apply _
    by_cases h4 : Nat.card B.Carrier = 4
    · exact Matrix.PSL3.BinaryOddCenterCover.exists_scalar_lift_four h4 e ho
    exact Matrix.PSL3.OrdinaryCenterRecognition.exists_scalar_lift h2 h4 e
  obtain ⟨k, hks, hk⟩ := hmap
  refine ⟨⟨k, hks, ?_⟩, hk⟩
  rw [← Matrix.PSL3.projection_ker B.Carrier]
  intro x hx
  change Matrix.PSL3.projection B.Carrier x = 1
  rw [← hk]
  change (centralQuotientCover e).toMonoidHom (k x) = 1
  rw [show k x = 1 from hx, map_one]

/-- The original cubic-ratio-two source input has precisely the two absolute
models in the existing sieve, with all actor and rank premises discharged. -/
theorem absolute_models (h : SourceHypothesis K ρ L) {B : BinaryField}
    (C : LinearCover B 3 L)
    (e : L ⧸ center L ≃* PSL(3,B.Carrier)) :
    let := h.finite_module
    let := inflated_irreducible ρ C h.irreducible
    0 < schurDegree (inflated ρ C) ∧
      ((schurDegree (inflated ρ C) = B.degree ∧
          Module.finrank (ZMod 2) V = 3 * B.degree ∧
          HasAbsoluteNaturalModel (inflated ρ C)) ∨
        (B.degree = 2 * schurDegree (inflated ρ C) ∧
          Module.finrank (ZMod 2) V = 9 * schurDegree (inflated ρ C) ∧
          HasAbsoluteTwistedModel (inflated ρ C) (schurDegree (inflated ρ C)))) := by
  let := h.finite_module
  let := inflated_irreducible ρ C h.irreducible
  exact absolute_models_of_estimates h C e
    (Matrix.PSL3Even.automorphism_two_rank_eq B.Carrier B.degree_pos B.card_eq).le
    (inner_word_estimate B (inflated ρ C) (inflated_central_kernel ρ C h.faithful))
    (inflated_outer_word_estimate h C)

end CFSG.Quasithin.ChapterK.Linear.Recognition.SourceFF
