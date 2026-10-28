module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.LocalGeometry.Submodules
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.LocalGeometry.Source

/-!
# The centerless shadow decomposition and full normality of its core

When Z(L) is trivial, the preparation hypotheses give
V ∩ L = Q = V ∩ L′. Each of the two full local normalizers generating M
preserves the corresponding intersection. Consequently Q is normal in M,
not merely in N_L(V).

The first local action has commutators in Q. Thus it preserves Q⟨r⟩ and
acts trivially on V/Q. The marked line ⟨z⟩ is fixed pointwise; multiplication
in the elementary shadow space gives a binary direct sum with dimensions
one and five. The decomposition equation explicitly intertwines the action.

The actual S₅ recognition, natural SL₂(4) chief-factor identification and
indecomposability are separate model calculations, not conclusions of this
module. The preparation and outer symmetry are explicit inputs here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.4.7, printed pp.1186–1187 (PDF pp.1203–1204).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow
variable {G : Type*} [Group G] [Finite G]

private theorem sup_zpowers_inf_eq (A B : Subgroup G) {x : G}
    (hx : orderOf x = 2) (hn : zpowers x ≤ normalizer (B : Set G))
    (hout : x ∉ B ⊔ A) : (B ⊔ zpowers x) ⊓ A = B ⊓ A := by
  classical
  apply le_antisymm _ (inf_le_inf_right _ le_sup_left)
  intro a ha
  have hb := ha.1
  change a ∈ ((B ⊔ zpowers x : Subgroup G) : Set G) at hb
  rw [coe_mul_of_right_le_normalizer_left _ _ hn] at hb
  obtain ⟨b, hb, t, ht, he⟩ := hb
  change t ∈ zpowers x at ht
  rw [mem_zpowers_iff_mem_range_orderOf, hx] at ht
  obtain ⟨n, hn, ht⟩ := Finset.mem_image.mp ht
  have hn2 := Finset.mem_range.mp hn
  interval_cases n
  · have ht1 : t = 1 := by simpa using ht.symm
    have hba : b = a := by simpa only [ht1, mul_one] using he
    exact ⟨hba ▸ hb, ha.2⟩
  · have htx : t = x := by simpa using ht.symm
    exfalso
    apply hout
    have hxa : x = b⁻¹ * a := by rw [← he, htx]; simp
    rw [hxa]
    exact (B ⊔ A).mul_mem ((show B ≤ B ⊔ A from le_sup_left) (B.inv_mem hb))
      ((show A ≤ B ⊔ A from le_sup_right) ha.2)

omit [Finite G] in
private theorem not_mem_of_center_eq_bot (A : Subgroup G) {x : G}
    (hc : center A = ⊥) (hx : x ≠ 1) (hcentral : x ∈ centralizer (A : Set G)) :
    x ∉ A := by
  intro hxA
  have hm : (⟨x, hxA⟩ : A) ∈ center A := by
    apply mem_center_iff.mpr
    intro a
    exact Subtype.ext (hcentral a a.property)
  rw [hc, mem_bot] at hm
  exact hx (congrArg Subtype.val hm)

omit [Finite G] in
private theorem outer_not_mem_product (A : Subgroup G) {x : G}
    (hn : x ∈ normalizer (A : Set G))
    (hout : A.normalizerMonoidHom ⟨x, hn⟩ ∉ MulAut.innerSubgroup A) :
    x ∉ A ⊔ centralizer (A : Set G) := by
  intro hx
  change x ∈ ((A ⊔ centralizer (A : Set G) : Subgroup G) : Set G) at hx
  rw [coe_mul_of_right_le_normalizer_left _ _ (centralizer_le_normalizer _)] at hx
  obtain ⟨a, ha, c, hc, he⟩ := hx
  apply hout
  refine ⟨⟨a, ha⟩, ?_⟩
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  change a * b * a⁻¹ = x * b * x⁻¹
  rw [← he, mul_inv_rev]
  have hcb := (mem_centralizer_iff.mp hc b b.property).symm
  calc
    a * b * a⁻¹ = a * (c * b * c⁻¹) * a⁻¹ := by rw [hcb, mul_assoc (b : G), mul_inv_cancel, mul_one]
    _ = a * c * b * (c⁻¹ * a⁻¹) := by group

private theorem core_intersection (A Q : Subgroup G) {s t : G}
    (hQ : Q ≤ A) (hcenter : center A = ⊥)
    (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hsC : s ∈ centralizer (A : Set G))
    (htout : t ∉ A ⊔ centralizer (A : Set G))
    (htN : zpowers t ≤ normalizer ((Q ⊔ zpowers s : Subgroup G) : Set G)) :
    (Q ⊔ (zpowers s ⊔ zpowers t)) ⊓ A = Q := by
  have hsout : s ∉ A := not_mem_of_center_eq_bot A hcenter
    (fun hh => by simp [hh] at hs) hsC
  have hsN : zpowers s ≤ normalizer (Q : Set G) := by
    apply (zpowers_le.mpr _).trans (centralizer_le_normalizer _)
    exact centralizer_le hQ hsC
  have h1 : (Q ⊔ zpowers s) ⊓ A = Q := by
    rw [sup_zpowers_inf_eq A Q hs hsN (by simpa [sup_eq_right.mpr hQ] using hsout),
      inf_eq_left.mpr hQ]
  rw [← sup_assoc, sup_zpowers_inf_eq A (Q ⊔ zpowers s) ht htN, h1]
  intro hh
  apply htout
  exact (sup_le (sup_le (hQ.trans le_sup_left)
    ((zpowers_le.mpr hsC).trans le_sup_right)) le_sup_left) hh

variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The centerless component meets V in exactly Q. -/
theorem centerless_shadow_inter_component (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hc : center L = ⊥) : shadowSpace L r z ⊓ L = residualCore L r := by
  have hzC : z ∈ centralizer (L : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (h.component.1 hx)
  have hrout : r ∉ L ⊔ centralizer (L : Set G) := by
    intro hh
    have hm : r ∈ innerPart L R := ⟨hr, hh⟩
    have hr1 : r = 1 := by simpa [hinner] using hm
    simp [hr1] at hr2
  have hn : zpowers r ≤ normalizer ((residualCore L r ⊔ zpowers z : Subgroup G) : Set G) := by
    apply le_trans (le_inf
      (residualCore_zpowers_r_centralize.trans (centralizer_le_normalizer _)) ?_)
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
    apply (zpowers_le.mpr _).trans (centralizer_le_normalizer _)
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact ((marked_involutions_commute h hr).zpow_right n).symm.eq
  change (residualCore L r ⊔ (zpowers r ⊔ zpowers z)) ⊓ L = _
  rw [sup_comm (zpowers r) (zpowers z)]
  exact core_intersection L (residualCore L r) (residualCore_le_component L r)
    hc h.involution hr2 hzC hrout hn

/-- Outer symmetry gives the same intersection with the conjugate component. -/
theorem centerless_shadow_inter_conjugate (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hc : center L = ⊥)
    (hsym : OuterFixedModel (L.conjBy g) z)
    (hQ : residualCore L r ≤ L.conjBy g) :
    shadowSpace L r z ⊓ L.conjBy g = residualCore L r := by
  have hc' : center (L.conjBy g) = ⊥ := by
    let e := (MulAut.conj g).subgroupMap L
    apply eq_bot_iff.mpr
    intro y hy
    have hx := ((centerCongr e).symm ⟨y, hy⟩).property
    change e.symm y ∈ center L at hx
    rw [hc, mem_bot] at hx
    exact (e.symm.map_eq_one_iff.mp hx)
  have hrC : r ∈ centralizer (L.conjBy g : Set G) := by
    have hh := map_centralizer_le_centralizer_image (L : Set G)
      (MulAut.conj g).toMonoidHom (h.sylow.le hr).1
    simpa only [conjBy, coe_map] using hh
  have hn : zpowers z ≤ normalizer ((residualCore L r ⊔ zpowers r : Subgroup G) : Set G) := by
    apply le_trans (le_inf
      ((residualCore_zpowers_centralize h).trans (centralizer_le_normalizer _)) ?_)
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
    apply (zpowers_le.mpr _).trans (centralizer_le_normalizer _)
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact ((marked_involutions_commute h hr).zpow_left n).eq
  exact core_intersection (L.conjBy g) (residualCore L r) hQ hc' hr2
    h.involution hrC (outer_not_mem_product _ hsym.normalizes hsym.outer) hn

/-- In the centerless case Q is normalized by both full local generators of M. -/
theorem centerless_shadowOvergroup_le_normalizer_core
    (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hc : center L = ⊥) (hsym : OuterFixedModel (L.conjBy g) z)
    (hQ : residualCore L r ≤ L.conjBy g) :
    shadowOvergroup L g r z ≤ normalizer (residualCore L r : Set G) := by
  have hn : normalizer ((centralizer (L : Set G)).conjBy g : Set G) =
      normalizer (L.conjBy g : Set G) := by
    change normalizer ((centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom : Set G) =
      normalizer (L.map (MulAut.conj g).toMonoidHom : Set G)
    rw [← map_equiv_normalizer_eq, ← map_equiv_normalizer_eq, h.normalizers_eq]
  apply sup_le
  · rw [← centerless_shadow_inter_component h hr hr2 hinner hc, inf_comm]
    exact inf_normalizer_le_normalizer_inf
  · rw [hn, ← centerless_shadow_inter_conjugate h hr hr2 hc hsym hQ, inf_comm]
    exact inf_normalizer_le_normalizer_inf

/-- The normality is relative to the full source overgroup M. -/
theorem centerless_core_normal_in_shadowOvergroup
    (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hc : center L = ⊥) (hsym : OuterFixedModel (L.conjBy g) z)
    (hQ : residualCore L r ≤ L.conjBy g) :
    ((residualCore L r).subgroupOf (shadowOvergroup L g r z)).Normal := by
  have hQM : residualCore L r ≤ shadowOvergroup L g r z := by
    apply le_trans _ (firstLocal_le_shadowOvergroup L g r z)
    exact le_inf (residualCore_le_component L r)
      ((show residualCore L r ≤ shadowSpace L r z from le_sup_left).trans
        (shadowSpace L r z).le_normalizer)
  exact (normal_subgroupOf_iff_le_normalizer hQM).mpr
    (centerless_shadowOvergroup_le_normalizer_core h hr hr2 hinner hc hsym hQ)

/-- The first local action is trivial on V/Q in the centerless case. -/
theorem centerless_firstLocal_commutator_le_core (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hc : center L = ⊥) :
    ⁅firstLocal L r z, shadowSpace L r z⁆ ≤ residualCore L r := by
  have hVN : shadowSpace L r z ≤ normalizer (L : Set G) := by
    apply sup_le ((residualCore_le_component L r).trans L.le_normalizer)
    apply sup_le (zpowers_le.mpr (h.sylow_normalizes (h.le_sylow hr)))
    apply (zpowers_le.mpr _).trans (centralizer_le_normalizer _)
    intro x hx
    exact mem_centralizer_singleton_iff.mp (h.component.1 hx)
  rw [← centerless_shadow_inter_component h hr hr2 hinner hc]
  exact le_inf (le_normalizer_iff_commutator_le_right.mp inf_le_right)
    ((commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hVN))

/-- Linear form of the trivial action on V/Q. -/
theorem centerless_firstLocal_displacement_mem_core
    (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hc : center L = ⊥) [IsElementaryAbelian 2 (shadowSpace L r z)]
    (a : firstLocal L r z) (v : Additive (shadowSpace L r z)) :
    shadowRepresentation L g r z
      (inclusion (firstLocal_le_shadowOvergroup L g r z) a) v - v ∈
      shadowSubspace L r z (residualCore L r) := by
  rw [mem_shadowSubspace, toMul_sub, Subgroup.coe_div, div_eq_mul_inv]
  rw [shadowRepresentation_apply]
  exact centerless_firstLocal_commutator_le_core h hr hr2 hinner hc
    (commutator_mem_commutator a.property v.toMul.property)

/-- The actual first local action fixes the specified marked vector. -/
theorem firstLocal_fixes_markedZ (h : IntersectionSetup T z L g R)
    [IsElementaryAbelian 2 (shadowSpace L r z)] (a : firstLocal L r z) :
    shadowRepresentation L g r z
      (inclusion (firstLocal_le_shadowOvergroup L g r z) a)
      (Additive.ofMul (markedZ L r z)) = Additive.ofMul (markedZ L r z) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (a : G) * z * (a : G)⁻¹ = z
  rw [mem_centralizer_singleton_iff.mp (h.component.1 a.property.1)]
  simp [mul_assoc]

/-- The five-space is invariant under the first local action. -/
theorem centerless_firstLocal_preserves_core_r (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hc : center L = ⊥) [IsElementaryAbelian 2 (shadowSpace L r z)]
    (a : firstLocal L r z) (v : Additive (shadowSpace L r z))
    (hv : v ∈ shadowSubspace L r z (residualCore L r ⊔ zpowers r)) :
    shadowRepresentation L g r z
      (inclusion (firstLocal_le_shadowOvergroup L g r z) a) v ∈
      shadowSubspace L r z (residualCore L r ⊔ zpowers r) := by
  have hd := centerless_firstLocal_displacement_mem_core h hr hr2 hinner hc a v
  have hd' : shadowRepresentation L g r z
      (inclusion (firstLocal_le_shadowOvergroup L g r z) a) v - v ∈
      shadowSubspace L r z (residualCore L r ⊔ zpowers r) :=
    (show residualCore L r ≤ residualCore L r ⊔ zpowers r from le_sup_left) hd
  simpa only [sub_add_cancel] using
    (shadowSubspace L r z (residualCore L r ⊔ zpowers r)).add_mem hd' hv

/-- The marked line and the five-space are complementary in the actual shadow space. -/
theorem shadowSubspace_markedZ_isCompl_core_r
    (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hzQ : z ∉ residualCore L r) [IsElementaryAbelian 2 (shadowSpace L r z)] :
    IsCompl (shadowSubspace L r z (zpowers z))
      (shadowSubspace L r z (residualCore L r ⊔ zpowers r)) := by
  classical
  let V := shadowSpace L r z
  let A := zpowers z
  let B := residualCore L r ⊔ zpowers r
  have hAV : A ≤ V := le_sup_right.trans le_sup_right
  have hBV : B ≤ V := sup_le le_sup_left (le_sup_left.trans le_sup_right)
  have hd : Disjoint A B := by
    apply Subgroup.disjoint_def.mpr
    intro x hxA hxB
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hxA
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hxA
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · simpa using he.symm
    · exact (marked_z_not_mem_core_r h hr hr2 hinner hzQ
        (by simpa only [← he, pow_one] using hxB)).elim
  let e : Subgroup V ≃o Submodule (ZMod 2) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)
  change IsCompl (e (A.subgroupOf V)) (e (B.subgroupOf V))
  apply e.isCompl_iff.mp
  constructor
  · apply Subgroup.disjoint_def.mpr
    intro x hxA hxB
    exact Subtype.ext (Subgroup.disjoint_def.mp hd hxA hxB)
  · rw [codisjoint_iff, ← subgroupOf_sup hAV hBV]
    have he : A ⊔ B = V := by
      dsimp [A, B, V, shadowSpace]
      ac_rfl
    rw [he, subgroupOf_self]

/-- The decomposition map is addition of the two actual embedded subspaces. -/
noncomputable def shadowMarkedDecomposition
    (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hzQ : z ∉ residualCore L r) [IsElementaryAbelian 2 (shadowSpace L r z)] :
    (shadowSubspace L r z (zpowers z) ×
      shadowSubspace L r z (residualCore L r ⊔ zpowers r)) ≃ₗ[ZMod 2]
      Additive (shadowSpace L r z) :=
  Submodule.prodEquivOfIsCompl _ _
    (shadowSubspace_markedZ_isCompl_core_r h hr hr2 hinner hzQ)

/-- The direct-sum coordinates retain the two original embeddings. -/
theorem shadowMarkedDecomposition_apply
    (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hzQ : z ∉ residualCore L r) [IsElementaryAbelian 2 (shadowSpace L r z)]
    (a : shadowSubspace L r z (zpowers z))
    (b : shadowSubspace L r z (residualCore L r ⊔ zpowers r)) :
    shadowMarkedDecomposition h hr hr2 hinner hzQ (a, b) = a.val + b.val := rfl

/-- The entire marked line is fixed pointwise. -/
theorem firstLocal_fixes_markedLine (h : IntersectionSetup T z L g R)
    [IsElementaryAbelian 2 (shadowSpace L r z)] (a : firstLocal L r z)
    (v : Additive (shadowSpace L r z)) (hv : v ∈ shadowSubspace L r z (zpowers z)) :
    shadowRepresentation L g r z
      (inclusion (firstLocal_le_shadowOvergroup L g r z) a) v = v := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [shadowRepresentation_apply]
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hv
  have hz : Commute (a : G) z := mem_centralizer_singleton_iff.mp
    (h.component.1 a.property.1)
  change z ^ n = (v.toMul : G) at hn
  change (a : G) * (v.toMul : G) * (a : G)⁻¹ = (v.toMul : G)
  rw [← hn, (hz.zpow_right n).eq]
  simp [mul_assoc]

/-- Equivariance of the direct sum: the first coordinate is fixed and the
second carries the restricted ambient action. -/
theorem centerless_shadowMarkedDecomposition_equivariant
    (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hzQ : z ∉ residualCore L r) (hc : center L = ⊥)
    [IsElementaryAbelian 2 (shadowSpace L r z)] (a : firstLocal L r z)
    (u : shadowSubspace L r z (zpowers z))
    (v : shadowSubspace L r z (residualCore L r ⊔ zpowers r)) :
    shadowRepresentation L g r z (inclusion (firstLocal_le_shadowOvergroup L g r z) a)
      (shadowMarkedDecomposition h hr hr2 hinner hzQ (u, v)) =
    shadowMarkedDecomposition h hr hr2 hinner hzQ
      (u, ⟨shadowRepresentation L g r z
        (inclusion (firstLocal_le_shadowOvergroup L g r z) a) v,
        centerless_firstLocal_preserves_core_r h hr hr2 hinner hc a v v.property⟩) := by
  rw [shadowMarkedDecomposition_apply, shadowMarkedDecomposition_apply, map_add,
    firstLocal_fixes_markedLine h a u u.property]

omit [Finite G] in
/-- Linearization retains the cardinality of every embedded subgroup. -/
theorem shadowSubspace_card (L A : Subgroup G) (r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)] (hA : A ≤ shadowSpace L r z) :
    Nat.card (shadowSubspace L r z A) = Nat.card A := by
  let e : shadowSubspace L r z A ≃ A := {
    toFun v := ⟨v.val.toMul, v.property⟩
    invFun a := ⟨Additive.ofMul ⟨a, hA a.property⟩, a.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact Nat.card_congr e

/-- The line generated by the marked involution has binary dimension one. -/
theorem shadowSubspace_markedLine_finrank (h : IntersectionSetup T z L g R)
    [IsElementaryAbelian 2 (shadowSpace L r z)] :
    Module.finrank (ZMod 2) (shadowSubspace L r z (zpowers z)) = 1 := by
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := shadowSubspace L r z (zpowers z))
  rw [shadowSubspace_card _ _ _ _ (le_sup_right.trans le_sup_right),
    Nat.card_zpowers, h.involution, Nat.card_zmod] at hd
  exact Nat.pow_right_injective (by decide : 1 < 2) hd.symm

/-- The complementary core-plus-involution space has binary dimension five. -/
theorem shadowSubspace_core_r_finrank (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hzQ : z ∉ residualCore L r) (hcard : Nat.card (residualCore L r) = 16)
    [IsElementaryAbelian 2 (shadowSpace L r z)] :
    Module.finrank (ZMod 2) (shadowSubspace L r z (residualCore L r ⊔ zpowers r)) = 5 := by
  have he := (shadowMarkedDecomposition h hr hr2 hinner hzQ).finrank_eq
  rw [Module.finrank_prod, shadowSubspace_markedLine_finrank h,
    shadowSpace_finrank _ _ _ (shadowSpace_card h hr hr2 hinner hzQ hcard)] at he
  omega

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow




