module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.SylowCenter
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.LocalFusion
public import Theory.GroupTheory.SubgroupCenterImageBound

/-!
# Noncommuting returning conjugates of the central J₂ involution

Two rows of the actual 128-element Sylow subgroup equal rows 1692 and 1395
of the checked centralizer enumeration. Its existing internal conjugating
words put both in the class of `FirstFusion.t`; their products differ at
permutation point 1. The whole Sylow-center calculation identifies every
original two-central marker with this class. Sylow conjugacy then places
the pair in the supplied Sylow subgroup.

Source: Aschbacher--Smith 1.1.5(3)(f), pp.501--503, and the Bender inspection
in Proposition 2.2.2, pp.519--520 (combined 1 March 2004 manuscript).
The retained ATLAS J2G1-p100B0 tables use Lean's left permutation action.
-/

public section
open Subgroup
open scoped Pointwise
namespace Sporadic.LeechRelated.J2
open GeneratorPair ExceptionalParabolics
open PairNormalizer PairNormalizer.SylowData SecondParabolic

private theorem row_check : ∀ p : Fin 100,
    sTable 83 p = FirstFusion.LocalCertificate.value 1692 p ∧
    sTable 106 p = FirstFusion.LocalCertificate.value 1395 p := by
  decide +kernel

private theorem square_check : (sTable 83) ^ 2 = 1 ∧ (sTable 106) ^ 2 = 1 := by
  decide +kernel

private theorem noncommuting_check :
    (sTable 83 * sTable 106) (1 : Fin 100) ≠ (sTable 106 * sTable 83) 1 := by
  decide +kernel

private theorem first_row : sElement 83 = FirstFusion.centralizerElement 1692 := by
  apply inclusion_injective
  apply Equiv.ext
  intro p
  rw [sElement_inclusion, FirstFusion.LocalCertificate.value_spec]
  exact (row_check p).1

private theorem second_row : sElement 106 = FirstFusion.centralizerElement 1395 := by
  apply inclusion_injective
  apply Equiv.ext
  intro p
  rw [sElement_inclusion, FirstFusion.LocalCertificate.value_spec]
  exact (row_check p).2

private theorem base_pair :
    ∃ a b : Seed.s, IsConj FirstFusion.t (a : Carrier) ∧
      IsConj FirstFusion.t (b : Carrier) ∧ ¬Commute a b := by
  have ha2 : sElement 83 ^ 2 = 1 := by
    apply inclusion_injective
    rw [map_pow, sElement_inclusion, map_one]
    exact square_check.1
  have hb2 : sElement 106 ^ 2 = 1 := by
    apply inclusion_injective
    rw [map_pow, sElement_inclusion, map_one]
    exact square_check.2
  have hab : ¬Commute (sElement 83) (sElement 106) := by
    intro h
    have he := congrArg (fun x : Carrier => inclusion x (1 : Fin 100)) h.eq
    simp only [map_mul, sElement_inclusion, Equiv.Perm.mul_apply] at he
    exact noncommuting_check he
  have han : sElement 83 ≠ 1 := by
    intro h
    apply hab
    rw [h]
    exact Commute.one_left _
  have hbn : sElement 106 ≠ 1 := by
    intro h
    apply hab
    rw [h]
    exact Commute.one_right _
  have ha := FirstFusion.LocalCertificate.fusion 1692 (first_row ▸ ha2) (first_row ▸ han)
  have hb := FirstFusion.LocalCertificate.fusion 1395 (second_row ▸ hb2) (second_row ▸ hbn)
  have htag1 : FirstFusion.LocalCertificate.fusionA 1692 = false := by decide +kernel
  have htag2 : FirstFusion.LocalCertificate.fusionA 1395 = false := by decide +kernel
  simp only [FirstFusion.LocalCertificate.base, htag1, Bool.false_eq_true, ↓reduceIte] at ha
  simp only [FirstFusion.LocalCertificate.base, htag2, Bool.false_eq_true, ↓reduceIte] at hb
  have ha' : IsConj FirstFusion.t (sElement 83) := by
    rw [first_row]
    exact ha
  have hb' : IsConj FirstFusion.t (sElement 106) := by
    rw [second_row]
    exact hb
  refine ⟨⟨sElement 83, sElement_mem 83⟩, ⟨sElement 106, sElement_mem 106⟩,
    ha', hb', ?_⟩
  intro h
  exact hab (h.map Seed.s.subtype)

private theorem central_marker_class (R : Sylow 2 Carrier)
    (v : Carrier) (hv : v ∈ R) (ho : orderOf v = 2)
    (hc : ∀ x ∈ R, Commute v x) : IsConj FirstFusion.t v := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier R (sylow FirstParabolic.card_l₁)
  let e := MulAut.conj g
  have hmap : (R : Subgroup Carrier).map e.toMonoidHom = Seed.s := by
    change ((g • R : Sylow 2 Carrier) : Subgroup Carrier) = Seed.s
    rw [hg]
    rfl
  have hvZ : v ∈ (center R).map (R : Subgroup Carrier).subtype := by
    refine ⟨⟨v, hv⟩, mem_center_iff.mpr ?_, rfl⟩
    intro x
    exact Subtype.ext (hc x x.property).symm.eq
  have himage := map_subgroup_center_le e.toMonoidHom (R : Subgroup Carrier)
    (mem_map_of_mem e.toMonoidHom hvZ)
  rw [hmap, center_s, mem_zpowers_iff_mem_range_orderOf, central_involution_order] at himage
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp himage
  have hi01 : i = 0 ∨ i = 1 := by
    have hi2 := Finset.mem_range.mp hi
    omega
  rcases hi01 with rfl | rfl
  · have hv1 : v = 1 := e.injective (by
      simpa only [pow_zero, map_one, MulEquiv.coe_toMonoidHom] using he.symm)
    simp [hv1] at ho
  · exact (isConj_iff.mpr ⟨g, by
      simpa only [pow_one, MulEquiv.coe_toMonoidHom, e, MulAut.conj_apply] using he.symm⟩).symm

/-- Every original two-central J₂ marker has noncommuting conjugates in its
supplied Sylow subgroup, with the marked class and conjugators proved internally. -/
theorem sylow_noncommuting_conjugates (R : Sylow 2 Carrier)
    (v : Carrier) (hv : v ∈ R) (ho : orderOf v = 2)
    (hc : ∀ x ∈ R, Commute v x) :
    ∃ a b : R, IsConj v (a : Carrier) ∧ IsConj v (b : Carrier) ∧ ¬Commute a b := by
  have hmarker := central_marker_class R v hv ho hc
  obtain ⟨a, b, ha, hb, hab⟩ := base_pair
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier (sylow FirstParabolic.card_l₁) R
  let e := MulAut.conj g
  have hmap : Seed.s.map e.toMonoidHom = (R : Subgroup Carrier) :=
    congrArg Sylow.toSubgroup hg
  have hmem (x : Seed.s) : e (x : Carrier) ∈ R := by
    change e (x : Carrier) ∈ (R : Subgroup Carrier)
    rw [← hmap]
    exact mem_map_of_mem e.toMonoidHom x.property
  refine ⟨⟨e a, hmem a⟩, ⟨e b, hmem b⟩,
    hmarker.symm.trans (ha.trans (isConj_iff.mpr ⟨g, rfl⟩)),
    hmarker.symm.trans (hb.trans (isConj_iff.mpr ⟨g, rfl⟩)), ?_⟩
  intro hcomm
  apply hab
  have hh := hcomm.map (R : Subgroup Carrier).subtype
  change Commute (e (a : Carrier)) (e (b : Carrier)) at hh
  exact Subtype.ext (Commute.of_map e.injective hh).eq

end Sporadic.LeechRelated.J2
