module
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.Geometry
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Mathlib.GroupTheory.Index

/-!
# Lifting the geometric placement problem from PSU₃ to SU₃

The full preimage of an odd subgroup has odd order because the scalar kernel
has odd order. The kernel has exponent dividing three, so cubing any lift of
a projective involution gives an involution with the same image. Normalization
and the literal isotropic-line no-Borel condition both pass to this preimage.
Consequently a construction of invariant orthogonal frames for SU₃ supplies
one for PSU₃. The construction itself remains an explicit premise.

Source: the two carrier alternatives in GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603.
-/

public section
open Subgroup
namespace UnitaryThree.OddTorusNormalizer
open BenderSuzuki.MatrixGroups
variable {E : Type*} [Field E]

/-- The complete preimage of an odd subgroup remains odd; the scalar kernel
is retained. -/
theorem odd_card_projective_preimage [Finite E] (J : HermitianForm 3 E)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hH : Odd (Nat.card H)) :
    Odd (Nat.card (H.comap J.specialToProjective)) := by
  let f := J.specialToProjective.comp (H.comap J.specialToProjective).subtype
  have hfker : f.ker = J.specialToProjective.ker.comap
      (H.comap J.specialToProjective).subtype := rfl
  have hk : Odd (Nat.card f.ker) := by
    rw [hfker]
    exact (J.odd_card_specialToProjective_ker).of_dvd_nat
      (card_comap_dvd_of_injective _ _ (H.comap J.specialToProjective).subtype_injective)
  have hr : f.range ≤ H := by
    rintro _ ⟨x, rfl⟩
    exact x.property
  rw [← f.ker.card_mul_index, index_ker]
  exact hk.mul (hH.of_dvd_nat (card_dvd_of_le hr))

/-- Cubing an arbitrary lift of a projective involution gives a genuine
special-unitary involution: the scalar kernel has exponent dividing three. -/
theorem exists_special_involution_lift (J : HermitianForm 3 E)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2) :
    ∃ s : J.specialSubgroup, orderOf s = 2 ∧ J.specialToProjective s = t := by
  obtain ⟨x, hx⟩ := J.specialToProjective_surjective t
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have htne : t ≠ 1 := by intro h; simp [h] at ht
  have hxker : x ^ 2 ∈ J.specialToProjective.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx, ht2]
  have hx6 : x ^ 6 = 1 := by
    have hc := congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x ^ 2, hxker⟩)
    simpa only [Subgroup.coe_pow, Subgroup.coe_mk, Subgroup.coe_one, ← pow_mul] using hc
  have himage : J.specialToProjective (x ^ 3) = t := by
    rw [map_pow, hx]
    calc
      t ^ 3 = t ^ 2 * t := pow_succ t 2
      _ = t := by rw [ht2, one_mul]
  refine ⟨x ^ 3, orderOf_eq_prime ?_ ?_, himage⟩
  · simpa only [← pow_mul] using hx6
  · intro he
    apply htne
    rw [← himage, he, map_one]

/-- Once the special-unitary geometric construction is supplied, full
preimages and involution lifts give that construction in the actual PSU₃.
No choice of a section or identification of the two carriers is used. -/
theorem projective_frame_of_special_frames [Finite E] (J : HermitianForm 3 E)
    (hspecial : ∀ (H : Subgroup J.specialSubgroup), Odd (Nat.card H) →
      ∀ t : J.specialSubgroup, orderOf t = 2 → t ∈ normalizer H →
        SpecialNoBorel J H → ∃ P : OrthogonalFrame J,
          H ⊔ zpowers t ≤ specialFrameStabilizer J P)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hH : Odd (Nat.card H))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : ProjectiveNoBorel J H) :
    ∃ P : OrthogonalFrame J, H ⊔ zpowers t ≤ projectiveFrameStabilizer J P := by
  obtain ⟨s, hs, hst⟩ := exists_special_involution_lift J t ht
  have hsH : s ∈ normalizer (H.comap J.specialToProjective) := by
    apply le_normalizer_comap J.specialToProjective
    change J.specialToProjective s ∈ normalizer H
    rwa [hst]
  obtain ⟨P, hP⟩ := hspecial (H.comap J.specialToProjective)
    (odd_card_projective_preimage J H hH) s hs hsH
    ((specialNoBorel_comap_iff J H).mpr hB)
  refine ⟨P, ?_⟩
  have hm : ((H.comap J.specialToProjective) ⊔ zpowers s).map J.specialToProjective =
      H ⊔ zpowers t := by
    rw [Subgroup.map_sup, map_comap_eq_self_of_surjective J.specialToProjective_surjective,
      MonoidHom.map_zpowers, hst]
  rw [← hm]
  apply (map_mono hP).trans
  rintro _ ⟨x, hx, rfl⟩
  rwa [specialFrameStabilizer_eq_comap] at hx

end UnitaryThree.OddTorusNormalizer
