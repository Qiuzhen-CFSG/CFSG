module
public import Theory.SpecificGroups.Rudvalis.TransitiveSixtyFourCentralizer
public import Theory.SpecificGroups.Rudvalis.Model.CubicElementary.Centralizers
public import Theory.GroupTheory.DoubleCoverCentralizer.SylowCenterConjugacy
public import Theory.GroupTheory.RadicalNormalizerControl
public import Theory.GroupTheory.PRadical
public import Theory.ElementaryAbelian.Injective

/-!
# Large central elementary subgroups in Rudvalis radical normalizers

An elementary subgroup E of order 64 contains every involution centralizing
it, by the native two-rank bound. It therefore contains a central-class
involution. The cubic incidence obstruction and the quintic point-core
obstruction make C(E) a two-group. If a two-radical P has E in its center,
N(P) preserves E. Radical normalizer control now gives P=C(E), so the
normalizers of P and E coincide. No maximality or ambient Sylow containment
of either normalizer is assumed.

Source: the Rudvalis local inspection in Aschbacher--Smith C.3.1 and 4.4.3,
printed pp.150--151,622--623; native two-rank and involution certificates
retain their ATLAS attribution in the imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.DoubleCoverCentralizer
open scoped IsMulCommutative
namespace Rudvalis

private theorem centralizing_involution_mem_sixtyFour
    (E : Subgroup Model) [IsElementaryAbelian 2 E] (hE : Nat.card E = 64)
    (x : Model) (hx : x ^ 2 = 1) (hc : x ∈ centralizer (E : Set Model)) : x ∈ E := by
  let C := E ⊔ zpowers x
  let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.sup_of_le_centralizer
    (zpowers_le.mpr hc)
  have hC : Nat.card C ≤ 64 := (primeRank_le_iff_elementary_card_le Model).mp
    primeRank_le_six C inferInstance
  have he : C = E := (eq_of_le_of_card_ge (show E ≤ C from le_sup_left)
    (by rw [hE]; exact hC)).symm
  exact he ▸ (show x ∈ C from mem_sup_right (mem_zpowers x))

private theorem sixtyFour_central_class
    (E : Subgroup Model) [IsElementaryAbelian 2 E] (hE : Nat.card E = 64) :
    ∃ z : E, IsConj (z : Model) (b ^ 2) := by
  obtain ⟨S,hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  let : Nontrivial (center S) := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [InvolutionCentralizers.sylow_center_card]; decide)
  obtain ⟨z,hz⟩ := exists_ne (1 : center S)
  have hz1 : ((z : S) : Model) ≠ 1 := fun he => hz (Subtype.ext (Subtype.ext he))
  have hzpow : (((z : S) : Model) ^ 2) = 1 := by
    have ho : orderOf z ∣ 2 := by
      simpa only [InvolutionCentralizers.sylow_center_card] using orderOf_dvd_natCard z
    exact congrArg (fun w : center S => ((w : S) : Model)) (orderOf_dvd_iff_pow_eq_one.mp ho)
  have hzC : ((z : S) : Model) ∈ centralizer (E : Set Model) := by
    intro y hy
    exact congrArg (S : Subgroup Model).subtype (mem_center_iff.mp z.property ⟨y,hES hy⟩)
  have hzE := centralizing_involution_mem_sixtyFour E hE z hzpow hzC
  refine ⟨⟨z,hzE⟩,?_⟩
  apply TwoCentral.isConj_of_center_card_two
    (show TwoCentral ((z : S) : Model) from ⟨S,z.val.property,z.property⟩)
    InvolutionCentralizers.square_twoCentral hz1 _ InvolutionCentralizers.sylow_center_card
  intro hb
  have hh := orderOf_dvd_of_pow_eq_one hb
  rw [orderOf_b] at hh
  norm_num at hh

/-- The full centralizer of any elementary order-64 subgroup in the native
Rudvalis carrier is a two-group. -/
theorem sixtyFour_centralizer_isPGroup
    (E : Subgroup Model) [IsElementaryAbelian 2 E] (hE : Nat.card E = 64) :
    IsPGroup 2 (centralizer (E : Set Model)) := by
  let C := centralizer (E : Set Model)
  obtain ⟨z,hclass⟩ := sixtyFour_central_class E hE
  have hCD : C ≤ centralizer ({(z : Model)} : Set Model) :=
    centralizer_le (Set.singleton_subset_iff.mpr z.property)
  have hthree : Nat.Coprime 3 (Nat.card C) := by
    apply (Nat.prime_three.coprime_iff_not_dvd).mpr
    intro hd
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 hd
    obtain ⟨U,hU⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2 (n := 4)
      (by rw [hE]; decide)
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective U.subtype U.subtype_injective
    let V := U.map E.subtype
    let : IsElementaryAbelian 2 V := IsElementaryAbelian.map E.subtype
    have hV : Nat.card V = 16 := (card_map_of_injective E.subtype_injective).trans hU
    apply CubicElementary.not_centralizes_elementary_sixteen V hV x ((orderOf_coe x).trans hx)
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (x.property y (map_subtype_le U hy))
  have hfive : Nat.Coprime 5 (Nat.card C) := by
    apply (Nat.prime_five.coprime_iff_not_dvd).mpr
    intro hd
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 5 hd
    exact sixtyFour_no_centralizing_five E hE z hclass x ((orderOf_coe x).trans hx) x.property
  apply isPGroup_iff_card_dvd_pow.mpr
  refine ⟨14,?_⟩
  have hd := card_dvd_of_le hCD
  rw [InvolutionCentralizers.first_centralizer_card hclass] at hd
  have hc : Nat.Coprime (Nat.card C) 15 := (hthree.mul_left hfive).symm
  exact hc.dvd_of_dvd_mul_right hd

/-- A native two-radical with a central elementary order-64 subgroup is its
full ambient centralizer; their full normalizers are therefore equal. -/
theorem radical_normalizer_eq_sixtyFour_normalizer
    (P E : Subgroup Model) (hP : P.IsPRadical 2) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 64) (hEP : E ≤ (center P).map P.subtype) :
    P = centralizer (E : Set Model) ∧ normalizer (P : Set Model) = normalizer (E : Set Model) := by
  have hPE : P ≤ centralizer (E : Set Model) := by
    intro p hp e he
    obtain ⟨z,hz,rfl⟩ := hEP he
    exact (congrArg P.subtype (mem_center_iff.mp hz ⟨p,hp⟩)).symm
  have hNPE : normalizer (P : Set Model) ≤ normalizer (E : Set Model) := by
    apply le_set_normalizer_iff.mpr
    intro g hg e he
    have hn := normalizer_le_normalizer_characteristic_image P (center P) hg
    have hz := (mem_normalizer_iff.mp hn e).mp (hEP he)
    have hzc : g * e * g⁻¹ ∈ centralizer (E : Set Model) := by
      obtain ⟨z,hz,hzval⟩ := hz
      intro y hy
      obtain ⟨w,hw,hwval⟩ := hEP hy
      rw [←hzval,←hwval]
      exact congrArg P.subtype (mem_center_iff.mp hz w)
    exact centralizing_involution_mem_sixtyFour E hE _
      (by rw [conj_pow,elemPow_eq_one_of_isElementaryAbelian e he,mul_one,mul_inv_cancel]) hzc
  have hCP : centralizer (E : Set Model) ≤ P :=
    le_of_normalizer_le_normalizer_of_pCore_normalizer_le P _ hP.isPGroup
      (sixtyFour_centralizer_isPGroup E hE) hP.2.le
      (hNPE.trans (normalizer_le_normalizer_centralizer E))
  have heq : P = centralizer (E : Set Model) := le_antisymm hPE hCP
  refine ⟨heq,le_antisymm hNPE ?_⟩
  rw [heq]
  exact normalizer_le_normalizer_centralizer E

end Rudvalis
