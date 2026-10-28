module
public import Theory.SpecificGroups.Suzuki.BorelResidualRigidity
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.ComponentInvolutionAction
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Centralizers of Suzuki Borel residuals in relative components

The residual of a lifted Borel covers the Suzuki quotient Borel, so it
contains a noncentral component element. Any element of the relative ambient
group centralizing this residual normalizes the component: distinct
components commute. Suzuki Borel rigidity kills its quotient action, and
perfectness lifts triviality across the retained central two-core.

This supplies the centralizer comparison in Aschbacher--Smith 15.1.21(i),
printed pp.1097--1098. It does not assume ambient normality of the component
or split its central cover.
-/

public section
open Subgroup Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H] {m : ℕ}

/-- The lifted Borel residual contains a noncentral element of the cover. -/
theorem suzuki_borelResidual_not_le_center (hm : 0 < m)
    (e : (H ⧸ pCore 2 H) ≃* SuzukiMatrixGroup m) (P : Sylow 2 H)
    (hc : center H = pCore 2 H) :
    ¬ (pResidual 2 (normalizer (P : Set H))).map
      (normalizer (P : Set H)).subtype ≤ center H := by
  intro h
  let q := QuotientGroup.mk' (pCore 2 H)
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hz : ((pResidual 2 (normalizer (P : Set H))).map
      (normalizer (P : Set H)).subtype).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q, QuotientGroup.ker_mk', ← hc] using h
  have hn := suzuki_borelResidual_quotient_image hm e P
  rw [hz] at hn
  change (⊥ : Subgroup (H ⧸ pCore 2 H)) = normalizer (Q : Set _) at hn
  have hQ : (Q : Subgroup (H ⧸ pCore 2 H)) = ⊥ := by
    apply bot_unique
    rw [hn]
    exact (Q : Subgroup (H ⧸ pCore 2 H)).le_normalizer
  have hcard := suzukiSylow_card hm e Q
  change Nat.card (Q : Subgroup (H ⧸ pCore 2 H)) = _ at hcard
  rw [hQ, card_bot] at hcard
  have hpow : 2 ≤ 2 ^ (2 * m + 1) := by
    simpa using Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ 2 * m + 1 by omega)
  nlinarith

/-- Centralizing the lifted Borel residual centralizes the original relative component. -/
theorem suzuki_borelResidual_relative_centralizer
    (A L : Subgroup G) (hLA : L ≤ A)
    (hL : IsComponent A (L.subgroupOf A))
    (hc : center L = pCore 2 L)
    (hm : 0 < m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m)
    (P : Sylow 2 L) :
    A ⊓ centralizer (((pResidual 2 (normalizer (P : Set L))).map
      (normalizer (P : Set L)).subtype).map L.subtype : Set G) ≤
      centralizer (L : Set G) := by
  let R := (pResidual 2 (normalizer (P : Set L))).map
    (normalizer (P : Set L)).subtype
  have hnR : ¬ R ≤ center L := suzuki_borelResidual_not_le_center hm e P hc
  obtain ⟨r, hr, hrc⟩ := Set.not_subset.mp hnR
  let K := L.subgroupOf A
  let rA : A := ⟨r, hLA r.property⟩
  have hrK : rA ∈ K := r.property
  have hrnon : rA ∉ centralizer (K : Set A) := by
    intro h
    apply hrc
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (congrArg (fun a : A => (a : G))
      (h ⟨y,hLA y.property⟩ (show (⟨y,hLA y.property⟩ : A) ∈ K from y.property)))
  let := hL.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLA)
  rintro x ⟨hxA,hxR⟩
  let xA : A := ⟨x,hxA⟩
  have hxr : Commute xA rA := by
    apply Subtype.ext
    exact (hxR r (mem_map_of_mem L.subtype hr)).symm
  have hxN : x ∈ normalizer (L : Set G) := by
    have hn := hL.normalizes_of_noncentral_element ⊥ bot_le xA rA hrK hrnon
      (hxr.map (QuotientGroup.mk' ⊥))
    rwa [← subgroupOf_normalizer_eq hLA] at hn
  let α := L.normalizerMonoidHom ⟨x,hxN⟩
  have hfix : ∀ z ∈ R, α z = z := by
    intro z hz
    apply Subtype.ext
    change x * (z : G) * x⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr (hxR z (mem_map_of_mem L.subtype hz)).symm
  have hquot := suzuki_quotientAut_eq_one_of_fixing_borelResidual hm e P α hfix
  have hα : α = 1 := by
    apply MulAut.eq_one_of_central_displacement
    intro z
    rw [hc]
    apply QuotientGroup.eq.mp
    have he := DFunLike.congr_fun hquot (QuotientGroup.mk' (pCore 2 L) z)
    rw [quotientAut_apply_mk] at he
    exact he.symm
  intro y hy
  have he := congrArg Subtype.val (DFunLike.congr_fun hα (⟨y,hy⟩ : L))
  change x * y * x⁻¹ = y at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end BenderSuzuki.MatrixGroups

