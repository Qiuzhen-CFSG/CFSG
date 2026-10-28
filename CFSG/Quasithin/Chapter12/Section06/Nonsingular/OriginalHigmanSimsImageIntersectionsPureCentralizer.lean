module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsImageIntersectionsPure

/-!
# The marked pure sixteen-subgroup is self-centralizing in HS

The marked subgroup contains the original elementary four-group, whose
full HS centralizer lies in the marked Sylow subgroup. The existing
512-row Sylow enumeration then checks that a row commuting with all
sixteen marked elements belongs to that same sixteen-subgroup.

This is an equality in the actual degree-100 ATLAS carrier. The finite
test uses the two point images already proved to distinguish Sylow rows;
no ambient centralizer or module assumption is supplied by the consumer.
Source: the HS inspection in Aschbacher--Smith 12.6.12, pp.825--826.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsImageIntersectionsNative
open Subgroup Theory.GroupTheory Sporadic.LeechRelated.HS
open EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData BlockNormalizer
open scoped IsMulCommutative
set_option maxRecDepth 10000

private theorem four_generator_points : ∀ (j : Fin 2) (p : Fin 100),
    point (candidateRow 0 (![2,12] j)) p =
      (elementaryGenerator j.castSucc : Equiv.Perm (Fin 100)) p := by
  apply allFin₂
  decide +kernel

private theorem four_le_markedW : elementary 1 ≤ markedW := by
  apply (closure_le _).mpr
  rintro x ⟨j,hj,rfl⟩
  have hj2 : j.val < 2 := by change j ≤ 1 at hj; omega
  let k : Fin 2 := ⟨j.val,hj2⟩
  refine ⟨![2,12] k,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rw [element_point]
  exact four_generator_points k p

private theorem sylow_centralizer_rows : ∀ i : Fin 512,
    (∀ j : Fin 16,
      point (candidateRow 0 j) (point i 1) = point i (point (candidateRow 0 j) 1) ∧
      point (candidateRow 0 j) (point i 4) = point i (point (candidateRow 0 j) 4)) →
    ∃ j : Fin 16, candidateRow 0 j = i := by
  apply allFin
  decide +kernel

/-- The full HS centralizer of the marked pure sixteen-subgroup is exactly
that same marked subgroup. -/
theorem markedW_centralizer : centralizer (markedW : Set Carrier) = markedW := by
  apply le_antisymm
  · intro x hx
    have hs : x ∈ subgroup := RankOneFourNormalizer.four_centralizer_le_sylow
      ((centralizer_le four_le_markedW) hx)
    obtain ⟨i,rfl⟩ := element_surjective hs
    obtain ⟨j,hj⟩ := sylow_centralizer_rows i (by
      intro j
      have he := hx (element (candidateRow 0 j)) (show element (candidateRow 0 j) ∈ markedW from ⟨j,rfl⟩)
      constructor
      · simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,element_point] using
          congrArg (fun a : Carrier => (a : Equiv.Perm (Fin 100)) 1) he
      · simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,element_point] using
          congrArg (fun a : Carrier => (a : Equiv.Perm (Fin 100)) 4) he)
    exact ⟨j,congrArg element hj⟩
  · let := markedW_elementary
    intro x hx y hy
    exact setLike_mul_comm hy hx

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsImageIntersectionsNative
