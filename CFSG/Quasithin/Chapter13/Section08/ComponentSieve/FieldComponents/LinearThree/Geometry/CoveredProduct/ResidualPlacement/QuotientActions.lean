module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.Notation
public import Theory.GroupTheory.PCoreImage

/-!
# Quotient actions of the covered residuals

The inverse image of the quotient center shows that L centralizes
L₀/O₂(L₀). The literal star map preserves residuals and identifies the
intrinsic two-core quotients. Only for a normal star image does it identify
the whole image with the intrinsic quotient; this distinction preserves the
possible two-core of L₀*.

An element normalizing X acts trivially on X/O₂(X) if it belongs to O₂(H),
or if X* is normal and that element centralizes X*. These commutator
calculations preserve inversion when adjusting the source element t.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), printed p.957, with Notation 13.2.1, printed p.877.
Normality, component centralization, and the inverter remain explicit
premises here; no covered branch or product decomposition is asserted.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G]

/-- The actual conjugation action of N_G(X) on X/O₂(X). -/
def coreAction (X : Subgroup G) : normalizer (X : Set G) →* MulAut (X ⧸ pCore 2 X) :=
  (quotientAut (pCore 2 X)).comp X.normalizerMonoidHom

/-- The quotient action retains the original conjugation on representatives. -/
theorem coreAction_mk (X : Subgroup G) (g : normalizer (X : Set G)) (x : X) :
    coreAction X g (QuotientGroup.mk' (pCore 2 X) x) =
      QuotientGroup.mk' (pCore 2 X) (X.normalizerMonoidHom g x) :=
  quotientAut_apply_mk _ _ _

/-- Intersection with an ambient two-core lies in the intrinsic two-core. -/
theorem core_intersection_le (H X : Subgroup G) (hXH : X ≤ H) :
    (pCore 2 H).comap (inclusion hXH) ≤ pCore 2 X :=
  le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective _ (inclusion_injective hXH)⟩

/-- Trivial quotient action is exactly the intrinsic two-core commutator condition. -/
theorem coreAction_eq_one_iff (X : Subgroup G) (g : normalizer (X : Set G)) :
    coreAction X g = 1 ↔ ∀ x : X, X.normalizerMonoidHom g x * x⁻¹ ∈ pCore 2 X := by
  constructor
  · intro h x
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 X) (X.normalizerMonoidHom g x * x⁻¹) = 1
    rw [map_mul, map_inv, ← coreAction_mk, h]
    exact mul_inv_cancel _
  · intro h
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) q
    rw [coreAction_mk]
    have he := (QuotientGroup.eq_one_iff _).mpr (h x)
    change QuotientGroup.mk' (pCore 2 X) (X.normalizerMonoidHom g x * x⁻¹) = 1 at he
    rw [map_mul, map_inv, mul_inv_eq_one] at he
    exact he

/-- Every element of L centralizes L₀/O₂(L₀), by the definition of O₂,Z(L). -/
theorem L_centralizes_zero_quotient (L : Subgroup G) (t : L) :
    coreAction (zero L) ⟨t.val, L_normalizes_zero L t.property⟩ = 1 := by
  apply (coreAction_eq_one_iff _ _).mpr
  intro x
  apply core_intersection_le L (zero L) (zero_le L)
  let q := QuotientGroup.mk' (pCore 2 L)
  let y : L := inclusion (zero_le L) x
  have hy : q y ∈ center (L ⧸ pCore 2 L) := by
    obtain ⟨a, ha, he⟩ := residual_le (centralPreimage L) x.property
    have hea : a = y := Subtype.ext he
    exact hea ▸ ha
  change inclusion (zero_le L)
    ((zero L).normalizerMonoidHom ⟨t.val, L_normalizes_zero L t.property⟩ x * x⁻¹)
      ∈ pCore 2 L
  have he : inclusion (zero_le L)
      ((zero L).normalizerMonoidHom ⟨t.val, L_normalizes_zero L t.property⟩ x * x⁻¹) =
      t * y * t⁻¹ * y⁻¹ := rfl
  rw [he]
  apply (QuotientGroup.eq_one_iff _).mp
  change q (t * y * t⁻¹ * y⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv,
    mem_center_iff.mp hy (q t)]
  group

/-- A normalizing element of O₂(H) has commutators with X in O₂(X). -/
theorem core_adjustment_commutator (H X : Subgroup G) (hXH : X ≤ H)
    (c : normalizer (X : Set G)) (hc : c.val ∈ H.pCoreIn 2) (x : X) :
    X.normalizerMonoidHom c x * x⁻¹ ∈ pCore 2 X := by
  apply core_intersection_le H X hXH
  change inclusion hXH (X.normalizerMonoidHom c x * x⁻¹) ∈ pCore 2 H
  obtain ⟨a, ha, he⟩ := hc
  have hcomm := (commutator_le_left (pCore 2 H) ⊤)
    (commutator_mem_commutator ha (mem_top (inclusion hXH x)))
  convert hcomm using 1
  apply Subtype.ext
  change c.val * x.val * c.val⁻¹ * x.val⁻¹ = a.val * x.val * a.val⁻¹ * x.val⁻¹
  change a.val = c.val at he
  rw [he]

/-- A normalizing element of the ambient two-core acts trivially on X/O₂(X). -/
theorem core_adjustment_action (H X : Subgroup G) (hXH : X ≤ H)
    (c : normalizer (X : Set G)) (hc : c.val ∈ H.pCoreIn 2) :
    coreAction X c = 1 := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) q
  rw [coreAction_mk]
  have h := (QuotientGroup.eq_one_iff
    (X.normalizerMonoidHom c x * x⁻¹)).mpr (core_adjustment_commutator H X hXH c hc x)
  change QuotientGroup.mk' (pCore 2 X) (X.normalizerMonoidHom c x * x⁻¹) = 1 at h
  rw [map_mul, map_inv, mul_inv_eq_one] at h
  exact h

/-- Multiplying an inverter by a normalizing element of O₂(H) preserves inversion. -/
theorem inversion_preserved_by_core_adjustment (H X : Subgroup G) (hXH : X ≤ H)
    (t c : normalizer (X : Set G)) (hc : c.val ∈ H.pCoreIn 2)
    (ht : ∀ q : X ⧸ pCore 2 X, coreAction X t q = q⁻¹) :
    ∀ q : X ⧸ pCore 2 X, coreAction X (t * c) q = q⁻¹ := by
  intro q
  rw [map_mul, core_adjustment_action H X hXH c hc, mul_one]
  exact ht q

/-- The literal map X → X* induced by inclusion in H and H → H/O₂(H). -/
def starMap (H X : Subgroup G) (hXH : X ≤ H) : X →* Source.starImage H X :=
  ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hXH)).codRestrict _
    (fun x => ⟨inclusion hXH x, x.property, rfl⟩)

/-- The source map is onto the actual star image. -/
theorem starMap_surjective (H X : Subgroup G) (hXH : X ≤ H) :
    Function.Surjective (starMap H X hXH) := by
  rintro ⟨_, h, hx, rfl⟩
  exact ⟨⟨h, hx⟩, Subtype.ext rfl⟩

/-- Its kernel is precisely the intersection with O₂(H). -/
theorem starMap_ker (H X : Subgroup G) (hXH : X ≤ H) :
    (starMap H X hXH).ker = (pCore 2 H).comap (inclusion hXH) := by
  ext x
  change (starMap H X hXH x = 1) ↔ inclusion hXH x ∈ pCore 2 H
  rw [← Subtype.coe_inj]
  exact QuotientGroup.eq_one_iff _

/-- The star map has two-group kernel, without subnormality of X. -/
theorem starMap_kernel_isPGroup (H X : Subgroup G) (hXH : X ≤ H) :
    IsPGroup 2 (starMap H X hXH).ker := by
  rw [starMap_ker]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hXH)

variable [Finite G]

/-- Each finite source residual is two-perfect. -/
theorem residual_isPPerfect (A : Subgroup G) : IsPPerfect 2 (residual A) :=
  isPPerfect_embedded_pResidual 2 A

/-- The star map preserves the full embedded residual, including any surviving two-core. -/
theorem star_residual (H A : Subgroup G) (hAH : A ≤ H) :
    Source.starImage H (residual A) = residual (Source.starImage H A) := by
  have he : (residual A).subgroupOf H = residual (A.subgroupOf H) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((residual_le A).trans hAH)]
    change residual A = ((pResidual 2 (A.subgroupOf H)).map (A.subgroupOf H).subtype).map H.subtype
    rw [map_embedded_pResidual, map_subgroupOf_eq_of_le hAH]
    rfl
  unfold Source.starImage
  rw [he]
  exact map_embedded_pResidual 2 _ _

/-- For arbitrary X ≤ H, identify the two-core quotients of X and X*; X* itself need not be cubic. -/
noncomputable def starCoreQuotientEquiv (H X : Subgroup G) (hXH : X ≤ H) :
    (X ⧸ pCore 2 X) ≃*
      (Source.starImage H X ⧸ pCore 2 (Source.starImage H X)) := by
  let f := (QuotientGroup.mk' (pCore 2 (Source.starImage H X))).comp (starMap H X hXH)
  have hs : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
    (starMap_surjective H X hXH)
  have hk : f.ker = pCore 2 X := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (starMap H X hXH).comap_pCore_of_ker_isPGroup
      (starMap_surjective H X hXH) (starMap_kernel_isPGroup H X hXH)
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hs)

/-- The quotient comparison is compatible with the original star map. -/
theorem starCoreQuotientEquiv_mk (H X : Subgroup G) (hXH : X ≤ H) (x : X) :
    starCoreQuotientEquiv H X hXH (QuotientGroup.mk' (pCore 2 X) x) =
      QuotientGroup.mk' (pCore 2 (Source.starImage H X)) (starMap H X hXH x) := rfl

private theorem star_twoCore_eq_bot (H : Subgroup G) : pCore 2 (Source.Hstar H) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have he := congrArg (map q) (q.comap_pCore_of_ker_isPGroup hs hk)
  rw [map_comap_eq_self_of_surjective hs] at he
  exact he.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))

/-- A normal subgroup of H/O₂(H) has trivial two-core. -/
theorem normal_star_twoCore (H X : Subgroup G) (hn : (Source.starImage H X).Normal) :
    pCore 2 (Source.starImage H X) = ⊥ := by
  let A := Source.starImage H X
  let : A.Normal := hn
  have hnormal : (A.pCoreIn 2).Normal :=
    inferInstanceAs (((pCore 2 A).map A.subtype).Normal)
  have hc : A.pCoreIn 2 ≤ pCore 2 (Source.Hstar H) :=
    le_sSup ⟨hnormal, isPGroup_pCoreIn 2 A⟩
  rw [star_twoCore_eq_bot H] at hc
  have he : (pCore 2 A).map A.subtype = (⊥ : Subgroup A).map A.subtype := by
    rw [Subgroup.map_bot]
    exact le_bot_iff.mp hc
  exact map_injective A.subtype_injective he

/-- Normality of X* identifies the kernel of X → X* with O₂(X). -/
theorem normal_starMap_ker (H X : Subgroup G) (hXH : X ≤ H)
    (hn : (Source.starImage H X).Normal) : (starMap H X hXH).ker = pCore 2 X := by
  have he := (starMap H X hXH).comap_pCore_of_ker_isPGroup
    (starMap_surjective H X hXH) (starMap_kernel_isPGroup H X hXH)
  rw [normal_star_twoCore H X hn] at he
  exact he

/-- Only after normality of X* is established, identify X/O₂(X) with X* itself. -/
noncomputable def normalStarEquiv (H X : Subgroup G) (hXH : X ≤ H)
    (hn : (Source.starImage H X).Normal) : (X ⧸ pCore 2 X) ≃* Source.starImage H X :=
  (QuotientGroup.quotientMulEquivOfEq (normal_starMap_ker H X hXH hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (starMap_surjective H X hXH))

/-- The normal-image equivalence preserves source representatives. -/
theorem normalStarEquiv_mk (H X : Subgroup G) (hXH : X ≤ H)
    (hn : (Source.starImage H X).Normal) (x : X) :
    (normalStarEquiv H X hXH hn (QuotientGroup.mk' (pCore 2 X) x) : Source.Hstar H) =
      QuotientGroup.mk' (pCore 2 H) (inclusion hXH x) := rfl

/-- A normal star image of a cubic two-core quotient has order three. -/
theorem normal_star_card_three (H X : Subgroup G) (hXH : X ≤ H)
    (hn : (Source.starImage H X).Normal) (hcard : Nat.card (X ⧸ pCore 2 X) = 3) :
    Nat.card (Source.starImage H X) = 3 :=
  (Nat.card_congr (normalStarEquiv H X hXH hn).toEquiv).symm.trans hcard

/-- Transport inversion through the actual source quotient and conjugation maps. -/
theorem normal_star_inversion (H X : Subgroup G) (hXH : X ≤ H)
    (hn : (Source.starImage H X).Normal) (t : normalizer (X : Set G)) (htH : t.val ∈ H)
    (hinv : ∀ q : X ⧸ pCore 2 X, coreAction X t q = q⁻¹) :
    ∀ x ∈ Source.starImage H X,
      QuotientGroup.mk' (pCore 2 H) ⟨t.val, htH⟩ * x *
        (QuotientGroup.mk' (pCore 2 H) ⟨t.val, htH⟩)⁻¹ = x⁻¹ := by
  rintro _ ⟨xH, hx, rfl⟩
  let x : X := ⟨xH.val, hx⟩
  have he := hinv (QuotientGroup.mk' (pCore 2 X) x)
  rw [coreAction_mk] at he
  have he' := congrArg (normalStarEquiv H X hXH hn) he
  rw [map_inv] at he'
  have hv := congrArg Subtype.val he'
  rw [normalStarEquiv_mk] at hv
  change QuotientGroup.mk' (pCore 2 H)
      ((⟨t.val, htH⟩ : H) * xH * (⟨t.val, htH⟩ : H)⁻¹) =
    (normalStarEquiv H X hXH hn (QuotientGroup.mk' (pCore 2 X) x) : Source.Hstar H)⁻¹ at hv
  rw [normalStarEquiv_mk, map_mul, map_mul, map_inv] at hv
  exact hv

/-- Centralization of the normal star image implies trivial action on X/O₂(X). -/
theorem coreAction_eq_one_of_star_centralizes (H X : Subgroup G) (hXH : X ≤ H)
    (hn : (Source.starImage H X).Normal) (c : normalizer (X : Set G)) (hcH : c.val ∈ H)
    (hc : QuotientGroup.mk' (pCore 2 H) ⟨c.val, hcH⟩ ∈
      centralizer (Source.starImage H X : Set (Source.Hstar H))) :
    coreAction X c = 1 := by
  apply (coreAction_eq_one_iff _ _).mpr
  intro x
  rw [← normal_starMap_ker H X hXH hn]
  apply MonoidHom.mem_ker.mpr
  apply Subtype.ext
  let q := QuotientGroup.mk' (pCore 2 H)
  let cH : H := ⟨c.val, hcH⟩
  let xH : H := inclusion hXH x
  change q (cH * xH * cH⁻¹ * xH⁻¹) = 1
  have hcomm : q xH * q cH = q cH * q xH := hc _ ⟨xH, x.property, rfl⟩
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
  group

/-- This also permits corrections whose star image survives, as for O₂(L₀). -/
theorem inversion_preserved_by_star_centralizer (H X : Subgroup G) (hXH : X ≤ H)
    (hn : (Source.starImage H X).Normal) (t c : normalizer (X : Set G)) (hcH : c.val ∈ H)
    (hc : QuotientGroup.mk' (pCore 2 H) ⟨c.val, hcH⟩ ∈
      centralizer (Source.starImage H X : Set (Source.Hstar H)))
    (ht : ∀ q : X ⧸ pCore 2 X, coreAction X t q = q⁻¹) :
    ∀ q : X ⧸ pCore 2 X, coreAction X (t * c) q = q⁻¹ := by
  intro q
  rw [map_mul, coreAction_eq_one_of_star_centralizes H X hXH hn c hcH hc, mul_one]
  exact ht q


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
