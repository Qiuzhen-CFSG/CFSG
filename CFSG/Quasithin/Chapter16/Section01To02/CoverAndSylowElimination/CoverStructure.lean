module
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.CoverInputs

/-!
# The elementary subgroup of the covered Suzuki case

The preimage of the quotient Sylow's eight-element involution subgroup has
exponent two: involutions lift, and any two lifts differ by an element of the
elementary center. This identifies that preimage with Ω₁(T_L), with central
index eight. Odd outer index then makes every involution in N_T(L) inner.
Its inducing element squares to one and normalizes T_L, hence lies in T_L
by Sylow maximality. This proves the starred product and centralization
assertions of 16.2.11 and retains the inducing element as an explicit witness.

The intrinsic hypotheses are precisely `SuzukiCoverInput`; no rank bound on
an unrelated ambient subgroup is assumed. The local placement of the external
conjugate, and the resulting exclusion, are separate arguments.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.2.2(4), p.409, and the proof of 16.2.11, p.1176.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16 CFSG.Quasithin.Chapter16.CoverAndSylowElimination

namespace CFSG.Quasithin.Chapter16.CoverAndSylowElimination
variable {G : Type*} [Group G] {T : Sylow 2 G} {z : G} {L : Subgroup G}

private theorem elementary_of_sq {M : Type*} [Group M] (h : ∀ x : M, x ^ 2 = 1) :
    IsElementaryAbelian 2 M :=
  { is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (h x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr h }

/-- Every lift of an element squaring to one also squares to one: two lifts
 differ by an element of the elementary central kernel. -/
theorem SuzukiCoverInput.sq_eq_one_of_quotient (d : SuzukiCoverInput T L)
    (x : L) (hx : (QuotientGroup.mk' (center L) x) ^ 2 = 1) : x ^ 2 = 1 := by
  let : IsElementaryAbelian 2 (center L) := d.center_elementary
  obtain ⟨y, hy, hq⟩ := d.involutions_lift x hx
  have hc : x / y ∈ center L := QuotientGroup.eq_iff_div_mem.mp hq.symm
  have hc2 : (x / y) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hc
  have hcomm : Commute (x / y) y := (mem_center_iff.mp hc y).symm
  simpa only [div_mul_cancel, hc2, hy, mul_one] using hcomm.mul_pow 2

/-- The cover center lies in the actual component Sylow, by I.2.2(4). -/
theorem SuzukiCoverInput.center_le_sylow (d : SuzukiCoverInput T L) :
    componentCenter L ≤ componentSylow T L := by
  rw [← d.center_sylow]
  exact map_subtype_le _

/-- The lift of the eight-element involution subgroup is precisely the first
omega subgroup, and its central quotient has order eight. -/
theorem SuzukiCoverInput.omega_structure (d : SuzukiCoverInput T L) :
    IsElementaryAbelian 2 (sylowOmega T L) ∧
      componentCenter L ≤ sylowOmega T L ∧
      (componentCenter L).relIndex (sylowOmega T L) = 8 := by
  obtain ⟨B, _, hBcard, hB⟩ := d.quotient_involutions
  let π := QuotientGroup.mk' (center L)
  let U := B.comap π
  have hCQ : center L ≤ (T : Subgroup G).subgroupOf L := by
    intro x hx
    exact (d.center_le_sylow (mem_map_of_mem L.subtype hx)).1
  have hUQ : U ≤ (T : Subgroup G).subgroupOf L := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (hB (π x)).mp hx |>.1
    have hd : y⁻¹ * x ∈ center L := QuotientGroup.eq.mp hyx
    simpa only [mul_inv_cancel_left] using
      ((T : Subgroup G).subgroupOf L).mul_mem hy (hCQ hd)
  have hpow (x : U) : x ^ 2 = 1 := by
    apply Subtype.ext
    exact d.sq_eq_one_of_quotient x ((hB (π x)).mp x.property).2
  let : IsElementaryAbelian 2 U := elementary_of_sq hpow
  have hCU : center L ≤ U := by
    intro x hx
    change π x ∈ B
    have hxπ : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hxπ]
    exact B.one_mem
  have hmap : U.map π = B := map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective _) _
  have hUZ : U.map L.subtype = sylowOmega T L := by
    apply le_antisymm
    · rintro x ⟨x, hx, rfl⟩
      have hxQ : (x : G) ∈ componentSylow T L := ⟨hUQ hx, x.property⟩
      refine ⟨⟨x, hxQ⟩, subset_closure ?_, rfl⟩
      change (⟨(x : G), hxQ⟩ : componentSylow T L) ^ (2 ^ 1) = 1
      apply Subtype.ext
      exact congrArg L.subtype (d.sq_eq_one_of_quotient x ((hB (π x)).mp hx).2)
    · apply map_le_iff_le_comap.mpr
      refine (closure_le _).mpr ?_
      intro x hx
      have hx2 : (x : G) ^ 2 = 1 := congrArg (componentSylow T L).subtype hx
      let xL : L := ⟨x, x.property.2⟩
      have hxU : xL ∈ U := by
        apply (hB (π xL)).mpr
        refine ⟨mem_map_of_mem π x.property.1, ?_⟩
        rw [← map_pow, show xL ^ 2 = 1 from Subtype.ext hx2, map_one]
      exact mem_map_of_mem L.subtype hxU
  refine ⟨hUZ ▸ IsElementaryAbelian.map L.subtype, ?_, ?_⟩
  · rw [← hUZ]
    exact map_mono hCU
  · rw [← hUZ, componentCenter, relIndex_map_map_of_injective _ _ L.subtype_injective]
    rw [← QuotientGroup.ker_mk' (center L), relIndex_ker, hmap, hBcard]

/-- An involution of the Sylow normalizer has the same action as an
involution in the component Sylow. The witness is retained explicitly. -/
theorem SuzukiCoverInput.involution_inner_witness [Finite G]
    (d : SuzukiCoverInput T L) (hlocal : CentralComponentSetup T z L)
    {a : G} (haT : a ∈ T) (haN : a ∈ normalizer (L : Set G)) (ha2 : a ^ 2 = 1) :
    ∃ b ∈ sylowOmega T L, b⁻¹ * a ∈ commutingSylow T L := by
  let an : normalizer (L : Set G) := ⟨a, haN⟩
  let α := L.normalizerMonoidHom an
  have hα2 : α ^ 2 = 1 := by
    change L.normalizerMonoidHom an ^ 2 = 1
    rw [← map_pow, show an ^ 2 = 1 from Subtype.ext ha2, map_one]
  obtain ⟨b, hb⟩ := MulAut.inner_of_sq_eq_one_of_odd_index d.odd_outer α hα2
  have hbC : b ^ 2 ∈ center L := by
    apply mem_center_iff.mpr
    intro x
    have he : MulAut.conj (b ^ 2) = 1 := by rw [map_pow, ← hb, hα2]
    have hx := DFunLike.congr_fun he x
    change b ^ 2 * x * (b ^ 2)⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  have hb2 : b ^ 2 = 1 := d.sq_eq_one_of_quotient b (by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hbC)
  obtain ⟨P, hP⟩ := hlocal.exists_component_sylow
  have hbn : b ∈ normalizer (P : Set L) := by
    rw [← P.coe_coe, hP]
    apply mem_normalizer_iff.mpr
    intro x
    have hx := congrArg L.subtype (DFunLike.congr_fun hb x)
    change a * (x : G) * a⁻¹ = ((b * x * b⁻¹ : L) : G) at hx
    change (x : G) ∈ T ↔ ((b * x * b⁻¹ : L) : G) ∈ T
    rw [← hx]
    exact (T : Subgroup G).le_normalizer haT x
  let : IsElementaryAbelian 2 (zpowers b) := IsElementaryAbelian.zpowers_of_pow_eq_one hb2
  have hbP : b ∈ P := by
    have hi := (IsElementaryAbelian.isPGroup 2 (zpowers b)).inf_normalizer_sylow P
    have hm : b ∈ zpowers b ⊓ normalizer (P : Set L) := ⟨mem_zpowers b, hbn⟩
    rw [hi] at hm
    exact hm.2
  have hbT : (b : G) ∈ T := by
    change b ∈ (P : Subgroup L) at hbP
    rw [hP] at hbP
    exact hbP
  have hbQ : (b : G) ∈ componentSylow T L := ⟨hbT, b.property⟩
  refine ⟨b, ⟨⟨b, hbQ⟩, subset_closure ?_, rfl⟩, ?_⟩
  · apply Subtype.ext
    exact congrArg L.subtype hb2
  · refine ⟨T.mul_mem (T.inv_mem hbT) haT, ?_⟩
    intro x hx
    have he := congrArg L.subtype (DFunLike.congr_fun hb ⟨x, hx⟩)
    change a * x * a⁻¹ = (b : G) * x * (b : G)⁻¹ at he
    have he' : a * x = (b : G) * x * (b : G)⁻¹ * a := mul_inv_eq_iff_eq_mul.mp he
    calc
      x * ((b : G)⁻¹ * a) = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹ * a) := by group
      _ = (b : G)⁻¹ * (a * x) := by rw [← he']
      _ = ((b : G)⁻¹ * a) * x := (mul_assoc _ _ _).symm

/-- The starred assertion of 16.2.11 at the original Sylow subgroup. -/
theorem SuzukiCoverInput.elementary_normalizer_action [Finite G]
    (d : SuzukiCoverInput T L) (hlocal : CentralComponentSetup T z L)
    (A : Subgroup G) (hAe : IsElementaryAbelian 2 A)
    (hAN : A ≤ (T : Subgroup G) ⊓ normalizer (L : Set G)) :
    A ≤ sylowOmega T L ⊔ commutingSylow T L ∧
      A ≤ centralizer (sylowOmega T L : Set G) := by
  let : IsElementaryAbelian 2 A := hAe
  let : IsElementaryAbelian 2 (sylowOmega T L) := d.omega_structure.1
  constructor
  · intro a ha
    obtain ⟨b, hb, hc⟩ := d.involution_inner_witness hlocal (hAN ha).1 (hAN ha).2
      (elemPow_eq_one_of_isElementaryAbelian a ha)
    simpa only [mul_inv_cancel_left] using
      (sylowOmega T L ⊔ commutingSylow T L).mul_mem ((le_sup_left : sylowOmega T L ≤ _) hb)
        ((le_sup_right : commutingSylow T L ≤ _) hc)
  · intro a ha
    obtain ⟨b, hb, hc⟩ := d.involution_inner_witness hlocal (hAN ha).1 (hAN ha).2
      (elemPow_eq_one_of_isElementaryAbelian a ha)
    have hbC : b ∈ centralizer (sylowOmega T L : Set G) := by
      intro x hx
      exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
        (⟨x, hx⟩ : sylowOmega T L) ⟨b, hb⟩)
    have hcC : b⁻¹ * a ∈ centralizer (sylowOmega T L : Set G) :=
      (centralizer_le (sylowOmega_le.trans inf_le_right)) hc.2
    simpa only [mul_inv_cancel_left] using
      (centralizer (sylowOmega T L : Set G)).mul_mem hbC hcC

open ChapterI.Section06To08

/-- Construct all the elementary structure and normalizer-action conclusions
used in the covered Suzuki argument, including their conjugates. -/
theorem SuzukiCoverInput.coverStructure [Finite G]
    (d : SuzukiCoverInput T L) (hlocal : CentralComponentSetup T z L) :
    CoverStructure T L := by
  obtain ⟨he, hc, hi⟩ := d.omega_structure
  refine ⟨he, hc, hi, ?_⟩
  intro g A hA hAN
  let : IsElementaryAbelian 2 A := hA
  have hAe : IsElementaryAbelian 2 (conjSubgroup A g⁻¹) :=
    IsElementaryAbelian.map (MulAut.conj g⁻¹).toMonoidHom
  have hback : conjSubgroup A g⁻¹ ≤ (T : Subgroup G) ⊓ normalizer (L : Set G) := by
    simpa only [conjSubgroup_inv] using conjSubgroup_mono hAN g⁻¹
  obtain ⟨hp, hcent⟩ := d.elementary_normalizer_action hlocal _ hAe hback
  have hcancel : conjSubgroup (conjSubgroup A g⁻¹) g = A := by
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  constructor
  · simpa only [hcancel] using conjSubgroup_mono hp g
  · have hh := (conjSubgroup_mono hcent g).trans
      (map_centralizer_le_centralizer_image (sylowOmega T L : Set G)
        (MulAut.conj g).toMonoidHom)
    change conjSubgroup (conjSubgroup A g⁻¹) g ≤ _ at hh
    rw [hcancel] at hh
    simpa only [conjSubgroup, Subgroup.coe_map] using hh

end CFSG.Quasithin.Chapter16.CoverAndSylowElimination
