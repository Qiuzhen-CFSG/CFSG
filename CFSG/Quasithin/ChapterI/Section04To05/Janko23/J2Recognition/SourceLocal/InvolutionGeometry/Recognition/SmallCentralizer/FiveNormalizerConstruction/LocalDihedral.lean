module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConsequences
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConstruction.LocalDihedral.Order
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConstruction.LocalDihedral.SourceReflection
public import Theory.GroupTheory.DihedralPresentation

/-!
# The literal local five-normalizer is dihedral

The order calculation gives |N_H(P)| = 20. Multiplying a generator of P
by the central involution z produces an element of order ten. An involution
inverting P inverts this product, and the two elements generate the whole
normalizer by its order. The dihedral presentation then gives an actual
multiplicative equivalence with `DihedralGroup 10`.

The source census supplies the inverting involution through the extraspecial
core and its A₅ quotient. Combining that construction with the presentation
proves the local normalizer isomorphism from the seed and census, without an
ambient order bound or simplicity assumption. The separate conditional
presentation theorem is retained for callers with an explicit inverter.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.1, printed p.260.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer

variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem dihedral_twenty_of_central_involution_and_inverter
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 20)
    (z p s : H) (hz : orderOf z = 2) (hp : orderOf p = 5)
    (hzC : z ∈ center H) (hs : s ^ 2 = 1) (hi : s * p * s⁻¹ = p⁻¹) :
    Nonempty (H ≃* DihedralGroup 10) := by
  let c := z * p
  have hzp : Commute z p := (mem_center_iff.mp hzC p).symm
  have hc : orderOf c = 10 := by
    rw [hzp.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hz, hp]; decide), hz, hp]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right
    (by
      have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
      simpa only [pow_two] using hz2)
  have hzfix : s * z * s⁻¹ = z :=
    mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp hzC s)
  have hconj : s * c * s⁻¹ = c⁻¹ := by
    change MulAut.conj s (z * p) = (z * p)⁻¹
    rw [map_mul]
    change (s * z * s⁻¹) * (s * p * s⁻¹) = (z * p)⁻¹
    rw [hzfix, hi, mul_inv_rev, hzi]
    exact (hzp.inv_right).eq
  let K := closure ({c, s} : Set H)
  have hcK : c ∈ K := subset_closure (by simp)
  have hsK : s ∈ K := subset_closure (by simp)
  have hCK : zpowers c ≤ K := zpowers_le.mpr hcK
  have hlarge : 10 < Nat.card K := by
    by_contra h
    have he : zpowers c = K := eq_of_le_of_card_ge hCK (by rw [Nat.card_zpowers, hc]; omega)
    have hsC : s ∈ zpowers c := he ▸ hsK
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hsC
    have hsc : Commute s c := hn ▸ (Commute.refl c).zpow_left n
    have heq : c = c⁻¹ :=
      (mul_inv_eq_iff_eq_mul.mpr hsc.eq).symm.trans hconj
    have hc2 : c ^ 2 = 1 := by
      simpa only [pow_two] using (mul_eq_one_iff_eq_inv.mpr heq)
    have hd := orderOf_dvd_of_pow_eq_one hc2
    rw [hc] at hd
    norm_num at hd
  have hdiv : 10 ∣ Nat.card K := by
    rw [← hc, ← Nat.card_zpowers]
    exact card_dvd_of_le hCK
  have hle : Nat.card K ≤ 20 := hH ▸ K.card_le_card_group
  have hcard : Nat.card K = 20 := by omega
  exact dihedralGroup_equiv_of_presentation (by decide) c s hc hs hconj
    (K.eq_top_of_card_eq (hcard.trans hH.symm)) hH

/-- An actual inverting involution discharges the remaining local presentation
premise. The normalizer order is proved from the original seed. -/
theorem exists_local_dihedral_equiv_of_inverter (D : Seed G)
    (P : Sylow 5 (involutionCentralizer D.z))
    (s : normalizer (P : Set (involutionCentralizer D.z))) (hs : s ^ 2 = 1)
    (hi : ∀ p ∈ (P : Subgroup (involutionCentralizer D.z)),
      (s : involutionCentralizer D.z) * p * (s : involutionCentralizer D.z)⁻¹ = p⁻¹) :
    Nonempty (normalizer ((P : Subgroup (involutionCentralizer D.z)) :
      Set (involutionCentralizer D.z)) ≃* DihedralGroup 10) := by
  let H := involutionCentralizer D.z
  let N := normalizer (P : Set H)
  let zH : H := ⟨D.z, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzHC : zH ∈ center H := by
    apply mem_center_iff.mpr
    intro a
    exact Subtype.ext (mem_centralizer_singleton_iff.mp a.property)
  have hzN : zH ∈ N :=
    centralizer_le_normalizer (P : Set H) (center_le_centralizer _ hzHC)
  let zN : N := ⟨zH, hzN⟩
  obtain ⟨p, hp⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [localFive_card])
  let pN : N := ⟨p, le_normalizer p.property⟩
  apply dihedral_twenty_of_central_involution_and_inverter
    (localFive_normalizer_card D P) zN pN s
  · exact (orderOf_coe _).symm.trans ((orderOf_coe _).symm.trans D.localType.involution)
  · exact (orderOf_coe pN).symm.trans ((orderOf_coe p).trans hp)
  · apply mem_center_iff.mpr
    intro n
    exact Subtype.ext (mem_center_iff.mp hzHC n)
  · exact hs
  · exact Subtype.ext (hi p p.property)

/-- The literal normalizer N_H(P) is dihedral of order twenty, as used in
the small-centralizer branch of 47.1. The reflection is constructed from
the source census, so no splitting or normalizer model is assumed. -/
theorem exists_local_dihedral_equiv (D : Seed G) (L : LocalCensus D)
    (P : Sylow 5 (involutionCentralizer D.z)) :
    Nonempty (normalizer ((P : Subgroup (involutionCentralizer D.z)) :
      Set (involutionCentralizer D.z)) ≃* DihedralGroup 10) := by
  obtain ⟨s, hs, hi⟩ := exists_local_five_reflection D L P
  exact exists_local_dihedral_equiv_of_inverter D P s hs hi

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer
