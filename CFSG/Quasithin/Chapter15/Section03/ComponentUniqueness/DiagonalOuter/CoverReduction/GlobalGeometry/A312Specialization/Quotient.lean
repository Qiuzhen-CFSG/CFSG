module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.ModelWitnesses
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# The actual two-core quotient in the A.3.12 specialization

The restriction of H → H/O₂(H) to any quasisimple subgroup has a central
2-group kernel. Its image is quasisimple; its two-core quotient is the
original two-core quotient. In particular the marking of B/O₂(B) as PSL₃(4)
survives, while its center can shrink from order four. No normality of B
in H or equality of the restriction kernel with O₂(B) is asserted.

Source: Aschbacher--Smith, A.3.12 (printed pp.47--48) and the proof of
15.3.38 (printed p.1136); the quotient steps are elementary group theory.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
variable {H : Type*} [Group H] [Finite H]

/-- The image under the literal ambient two-core quotient. -/
abbrev image (B : Subgroup H) := B.map (QuotientGroup.mk' (pCore 2 H))

/-- The surjective restriction to the actual image. -/
def imageMap (B : Subgroup H) : B →* image B :=
  (QuotientGroup.mk' (pCore 2 H)).subgroupMap B

omit [Finite H] in
theorem imageMap_surjective (B : Subgroup H) : Function.Surjective (imageMap B) :=
  (QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective B

omit [Finite H] in
theorem imageMap_ker_isTwoGroup (B : Subgroup H) : IsPGroup 2 (imageMap B).ker := by
  rw [imageMap, ker_subgroupMap, QuotientGroup.ker_mk']
  exact pCore_isPGroup.comap_of_injective B.subtype B.subtype_injective

omit [Finite H] in
/-- Only inclusion, rather than equality, holds for an arbitrary B. -/
theorem imageMap_ker_le_twoCore (B : Subgroup H) : (imageMap B).ker ≤ pCore 2 B :=
  le_sSup ⟨inferInstance, imageMap_ker_isTwoGroup B⟩

/-- A quasisimple subgroup cannot disappear into the ambient two-core. -/
theorem image_nontrivial (B : Subgroup H) [IsQuasisimple B] : Nontrivial (image B) := by
  apply (nontrivial_iff_ne_bot _).mpr
  intro hb
  have hle : B ≤ pCore 2 H := by
    intro b hb'
    have he := mem_map_of_mem (QuotientGroup.mk' (pCore 2 H)) hb'
    change _ ∈ image B at he
    rw [hb, mem_bot] at he
    exact (QuotientGroup.eq_one_iff b).mp he
  have hp : IsPGroup 2 B := pCore_isPGroup.to_le hle
  let : Group.IsNilpotent B := hp.isNilpotent
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  exact Group.IsPerfect.not_isSolvable B inferInstance

theorem image_quasisimple (B : Subgroup H) [IsQuasisimple B] : IsQuasisimple (image B) := by
  let := image_nontrivial B
  exact IsQuasisimple.of_surjective (imageMap B) (imageMap_surjective B)

/-- The image map is a perfect central cover, with its original kernel. -/
def imageCover (B : Subgroup H) [IsQuasisimple B] :
    PerfectCentralCovering.Cover B (image B) where
  toMonoidHom := imageMap B
  surjective := imageMap_surjective B
  isPerfect := inferInstance
  ker_le_center := (imageMap_ker_le_twoCore B).trans (IsQuasisimple.pCore_le_center 2)

theorem image_center (B : Subgroup H) [IsQuasisimple B] :
    center (image B) = (center B).map (imageMap B) := by
  have hc : (center (image B)).comap (imageMap B) = center B :=
    (imageCover B).comap_center
  rw [← hc, map_comap_eq_self]
  rw [(imageMap B).range_eq_top_of_surjective (imageMap_surjective B)]
  exact le_top

theorem image_twoCore (B : Subgroup H) :
    pCore 2 (image B) = (pCore 2 B).map (imageMap B) := by
  rw [← (imageMap B).comap_pCore_of_ker_isPGroup (imageMap_surjective B)
    (imageMap_ker_isTwoGroup B), map_comap_eq_self]
  rw [(imageMap B).range_eq_top_of_surjective (imageMap_surjective B)]
  exact le_top

theorem image_center_eq_twoCore (B : Subgroup H) [IsQuasisimple B]
    (hZ : center B = pCore 2 B) : center (image B) = pCore 2 (image B) := by
  rw [image_center, hZ, image_twoCore]

theorem image_center_card_le (B : Subgroup H) [IsQuasisimple B] :
    Nat.card (center (image B)) ≤ Nat.card (center B) := by
  rw [image_center]
  exact Nat.card_le_card_of_surjective _ ((imageMap B).subgroupMap_surjective (center B))

/-- Quotient the image by its own two-core; this restores the original quotient. -/
def imageTwoCoreEquiv (B : Subgroup H) :
    (B ⧸ pCore 2 B) ≃* (image B ⧸ pCore 2 (image B)) := by
  let f := (QuotientGroup.mk' (pCore 2 (image B))).comp (imageMap B)
  have hk : f.ker = pCore 2 B := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (imageMap B).comap_pCore_of_ker_isPGroup (imageMap_surjective B)
      (imageMap_ker_isTwoGroup B)
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk'_surjective _).comp (imageMap_surjective B)))

theorem imageTwoCoreEquiv_mk (B : Subgroup H) (x : B) :
    imageTwoCoreEquiv B (QuotientGroup.mk' (pCore 2 B) x) =
      QuotientGroup.mk' (pCore 2 (image B)) (imageMap B x) := rfl

/-- The concrete coefficient field and projective model survive unchanged. -/
def imageMarking (B : Subgroup H) (c : ProjectiveMarking B 4) :
    ProjectiveMarking (image B) 4 where
  F := c.F
  card := c.card
  equivalence := (imageTwoCoreEquiv B).symm.trans c.equivalence

omit [Finite H] in
theorem marked_quotient_card (B : Subgroup H) (c : ProjectiveMarking B 4) :
    Nat.card (B ⧸ pCore 2 B) = 20160 := by
  rw [Nat.card_congr c.equivalence.toEquiv, Matrix.PSL3.LinearThree.card_projective, c.card]
  norm_num

omit [Finite H] in
theorem marked_card_dvd (B : Subgroup H) (c : ProjectiveMarking B 4) :
    20160 ∣ Nat.card B := by
  rw [← marked_quotient_card B c]
  exact card_quotient_dvd_card (pCore 2 B)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
