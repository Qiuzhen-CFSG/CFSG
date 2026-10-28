module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.CoveredCase.Diagnostics
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.Fusion
public import Theory.GroupAction.SylowPointwiseInner

/-!
# The whole Sylow and its omega subgroup in the covered case

Odd outer index and Sylow maximality give T = T_L T_C. Involutory
representatives and the elementary omega configuration give V = Ω₁(T),
hence weak closure and a normalizer fusion mover. The intersection with
C_G(L) is exactly Ω₁(T_C), with the cover center retained in that factor.

Source: Aschbacher–Smith, 16.5.1, printed pp.1193–1195; 16.1.2,
p.1170; I.2.2(4), p.409, manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
open CFSG.Quasithin.Chapter16 CFSG.Quasithin.Chapter16.CoverAndSylowElimination
open CFSG.Quasithin.Chapter16.Intersections CFSG.Quasithin.Chapter16.Intersections.Bender
open CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.CoveredCase
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G} {z : G}

theorem space_eq_omega (h : StandardSetup T z L) (d : SuzukiCoverInput T L)
    [IsElementaryAbelian 2 (benderSpace T L)] :
    benderSpace T L = omegaOneAmbient (T : Subgroup G) := by
  let : IsElementaryAbelian 2 (sylowOmega T L) := d.omega_structure.1
  apply le_antisymm
  · intro v hv
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl v (benderSpace_le_sylow T L hv)
      (elemPow_eq_one_of_isElementaryAbelian v hv)
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro t ht ht2
    obtain ⟨b, hb, hc⟩ := d.involution_inner_witness h.toCentralComponentSetup ht
      (h.sylow_normalizes ht) ht2
    have hb2 : b ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian b hb
    have hcomm : Commute b (b⁻¹ * t) := (hc.2 b (sylowOmega_le hb).2)
    have hc2 : (b⁻¹ * t) ^ 2 = 1 := by
      have hh := hcomm.mul_pow 2
      simpa only [mul_inv_cancel_left, ht2, hb2, one_mul] using hh.symm
    have hcW : b⁻¹ * t ∈ omegaOneAmbient (commutingSylow T L) :=
      (omegaOneAmbient_le_iff _ _).mp le_rfl _ hc hc2
    have hh := (benderSpace T L).mul_mem ((show sylowOmega T L ≤ benderSpace T L from le_sup_right) hb)
      ((show omegaOneAmbient (commutingSylow T L) ≤ benderSpace T L from le_sup_left) hcW)
    simpa only [mul_inv_cancel_left] using hh

theorem space_weakly_closed (h : StandardSetup T z L) (d : SuzukiCoverInput T L)
    [IsElementaryAbelian 2 (benderSpace T L)] (a : G)
    (ha : (benderSpace T L).conjBy a ≤ (T : Subgroup G)) :
    (benderSpace T L).conjBy a = benderSpace T L := by
  have he : IsElementaryAbelian 2 ((benderSpace T L).conjBy a) :=
    IsElementaryAbelian.map (MulAut.conj a).toMonoidHom
  let := he
  apply eq_of_le_of_card_ge
  · intro v hv
    rw [space_eq_omega h d]
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl v (ha hv)
      (elemPow_eq_one_of_isElementaryAbelian v hv)
  · exact (card_map_of_injective (MulAut.conj a).injective).ge

omit [Finite G] in
theorem space_centralizer_intersection (d : SuzukiCoverInput T L) :
    benderSpace T L ⊓ centralizer (L : Set G) =
      omegaOneAmbient (commutingSylow T L) := by
  apply le_antisymm
  · intro v hv
    have hcomm : omegaOneAmbient (commutingSylow T L) ≤
        centralizer (omegaOneAmbient (componentSylow T L) : Set G) :=
      ((omegaOneAmbient_le _).trans inf_le_right).trans
        (centralizer_le ((omegaOneAmbient_le _).trans inf_le_right))
    have hvp : v ∈ (omegaOneAmbient (commutingSylow T L) : Set G) *
        (omegaOneAmbient (componentSylow T L) : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _
        (hcomm.trans (centralizer_le_normalizer _))]
      exact hv.1
    obtain ⟨w, hw, a, ha, rfl⟩ := hvp
    have hwC : w ∈ centralizer (L : Set G) := (omegaOneAmbient_le _ hw).2
    have haC : a ∈ centralizer (L : Set G) := by
      simpa only [inv_mul_cancel_left] using
        (centralizer (L : Set G)).mul_mem ((centralizer _).inv_mem hwC) hv.2
    have haZ : a ∈ componentCenter L := by
      refine ⟨⟨a, (omegaOneAmbient_le _ ha).2⟩, ?_, rfl⟩
      exact mem_center_iff.mpr fun b => Subtype.ext (haC b b.property)
    exact (omegaOneAmbient _).mul_mem hw (center_le_commuting_omega d haZ)
  · exact le_inf le_sup_left ((omegaOneAmbient_le _).trans inf_le_right)

/-- Odd outer index makes every element of T inner on L, with its representative in T_L. -/
theorem sylow_inner_witness (h : StandardSetup T z L) (d : SuzukiCoverInput T L)
    {a : G} (ha : a ∈ T) :
    ∃ b ∈ componentSylow T L, b⁻¹ * a ∈ commutingSylow T L := by
  let an : normalizer (L : Set G) := ⟨a, h.sylow_normalizes ha⟩
  let α := L.normalizerMonoidHom an
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨a, ha⟩
  have ha2 : a ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hα2 : α ^ (2 ^ k) = 1 := by
    change L.normalizerMonoidHom an ^ (2 ^ k) = 1
    rw [← map_pow, show an ^ (2 ^ k) = 1 from Subtype.ext ha2, map_one]
  obtain ⟨b, hb⟩ := MulAut.inner_of_two_pow_eq_one_of_odd_index d.odd_outer α hα2
  have hbC : b ^ (2 ^ k) ∈ center L := by
    apply mem_center_iff.mpr
    intro x
    have he : MulAut.conj (b ^ (2 ^ k)) = 1 := by rw [map_pow, ← hb, hα2]
    have hx := DFunLike.congr_fun he x
    change b ^ (2 ^ k) * x * (b ^ (2 ^ k))⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  let := d.center_elementary
  have hb2 : b ^ (2 ^ (k+1)) = 1 := by
    rw [pow_succ, pow_mul]
    exact elemPow_eq_one_of_isElementaryAbelian _ hbC
  have hp : IsPGroup 2 (zpowers b) := isPGroup_iff_card_dvd_pow.mpr
    ⟨k+1, by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hb2⟩
  obtain ⟨P, hP⟩ := h.toCentralComponentSetup.exists_component_sylow
  have hbn : b ∈ normalizer (P : Set L) := by
    rw [← P.coe_coe, hP]
    apply mem_normalizer_iff.mpr
    intro x
    have hx := congrArg L.subtype (DFunLike.congr_fun hb x)
    change a * (x : G) * a⁻¹ = ((b * x * b⁻¹ : L) : G) at hx
    change (x : G) ∈ T ↔ ((b * x * b⁻¹ : L) : G) ∈ T
    rw [← hx]
    exact (T : Subgroup G).le_normalizer ha x
  have hbP : b ∈ P := by
    have hi := hp.inf_normalizer_sylow P
    have hm : b ∈ zpowers b ⊓ normalizer (P : Set L) := ⟨mem_zpowers b, hbn⟩
    rw [hi] at hm
    exact hm.2
  have hbT : (b : G) ∈ T := by
    change b ∈ (P : Subgroup L) at hbP
    rw [hP] at hbP
    exact hbP
  refine ⟨b, ⟨hbT, b.property⟩, ⟨T.mul_mem (T.inv_mem hbT) ha, ?_⟩⟩
  intro x hx
  have he := congrArg L.subtype (DFunLike.congr_fun hb ⟨x, hx⟩)
  change a * x * a⁻¹ = (b : G) * x * (b : G)⁻¹ at he
  have he' : a * x = (b : G) * x * (b : G)⁻¹ * a := mul_inv_eq_iff_eq_mul.mp he
  calc
    x * ((b : G)⁻¹ * a) = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹ * a) := by group
    _ = (b : G)⁻¹ * (a * x) := by rw [← he']
    _ = ((b : G)⁻¹ * a) * x := (mul_assoc _ _ _).symm

theorem sylow_eq_sup (h : StandardSetup T z L) (d : SuzukiCoverInput T L) :
    (T : Subgroup G) = componentSylow T L ⊔ commutingSylow T L := by
  apply le_antisymm
  · intro t ht
    obtain ⟨s, hs, hc⟩ := sylow_inner_witness h d ht
    have hh := mul_mem_sup hs hc
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le inf_le_left inf_le_left

theorem covered_fusion_mover {g : G} {R : Subgroup G}
    (h : IntersectionSetup T z L g R) (d : SuzukiCoverInput T L)
    [IsElementaryAbelian 2 (benderSpace T L)]
    (hconj : R = (commutingSylow T L).conjBy g)
    (hU : omegaOneAmbient R ≤ benderSpace T L) :
    ∃ a ∈ normalizer (benderSpace T L : Set G),
      (omegaOneAmbient (commutingSylow T L)).conjBy a = omegaOneAmbient R :=
  fusion_mover (space_weakly_closed h.toStandardSetup d) hconj hU

omit [Finite G] in
theorem disjoint_omegas {R : Subgroup G}
    (hfaith : Disjoint R (centralizer (L : Set G))) :
    Disjoint (omegaOneAmbient (commutingSylow T L)) (omegaOneAmbient R) :=
  (hfaith.mono (omegaOneAmbient_le _) ((omegaOneAmbient_le _).trans inf_le_right)).symm

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.CoveredCase
