module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BorelFields
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.Theta
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelInvariantRoot
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.CubicBorelFixer
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# The linear-three Borel, including central two-covers

In the projective model, the normal four-group contains the Sylow centre:
Borel invariance and root-scalar transitivity force this containment. Its
order bounds the field by four, hence the larger-field degree is two.

The upstairs centralizer calculation works at every positive even degree.
Order-three elements lift through the central two-kernel. An element fixing
`Y₊` therefore fixes all cubic elements of the projective Borel. Their
pointwise automorphism fixer is trivial. Perfectness of the original
component makes descent through its centre faithful, giving the literal
equality `C_S(Y₊) = C_S(L)` even for the nontrivial central covers.

The Borel identification remains an explicit prerequisite from the separate
parabolic inspection. Source: Aschbacher--Smith, combined manuscript
(1 March 2004), proof of 15.3.43, printed p.1140.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterF.Source
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

omit [Finite G] in
private theorem sylow_normalizer_map_subtype
    (T : Sylow 2 L) (hT : (T : Subgroup L).map L.subtype = S ⊓ L) :
    (normalizer (T : Set L)).map L.subtype = borel L S := by
  have hTL : (S ⊓ L).subgroupOf L = (T : Subgroup L) := by
    rw [← hT]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  change (normalizer ((T : Subgroup L) : Set L)).map L.subtype = _
  rw [← hTL, ← subgroupOf_normalizer_eq inf_le_right, subgroupOf_map_subtype]
  exact inf_comm _ _

omit [Finite G] in
private theorem modelMap_ker {H : Type*} [Group H]
    (e : (L ⧸ center L) ≃* H) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (center L))).ker = center L := by
  ext x
  change e (QuotientGroup.mk' (center L) x) = 1 ↔ x ∈ center L
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

/-- The field bound uses the moving normal plane and the genuine projective
root centre; no triviality of the component centre is assumed. -/
theorem linear_three_borel_degree_eq_two
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n))
    (hB : M ⊓ L = borel L S) : n = 2 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let f : L →* PSL(3,F) := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center L := modelMap_ker e
  obtain ⟨T, hT⟩ := component_sylow c
  let P := T.mapSurjective hf
  let W := (V₂.subgroupOf L).map f
  have hVL := plane_le_component c
  have hTL : (S ⊓ L).subgroupOf L = (T : Subgroup L) := by
    rw [← hT]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hWP : W ≤ (P : Subgroup PSL(3,F)) := by
    apply map_mono
    rw [← hTL]
    exact subgroupOf_mono L (le_inf c.plane_two_le hVL)
  have hTW : normalizer (T : Set L) ≤ normalizer (V₂.subgroupOf L : Set L) := by
    change normalizer ((T : Subgroup L) : Set L) ≤ _
    rw [← hTL, ← subgroupOf_normalizer_eq inf_le_right,
      ← subgroupOf_normalizer_eq hVL]
    intro x hx
    exact borel_normalizes_plane c hB ⟨x.property, hx⟩
  have hBW : normalizer (P : Set PSL(3,F)) ≤ normalizer (W : Set PSL(3,F)) := by
    change normalizer ((T : Subgroup L).map f : Set PSL(3,F)) ≤ _
    rw [← T.normalizer_map_surjective f hf]
    exact (map_mono hTW).trans ((V₂.subgroupOf L).le_normalizer_map f)
  have hWne : W ≠ ⊥ := by
    intro hzero
    have hVC : V₂ ≤ centralizer (Yplus : Set G) := by
      have hker := (map_eq_bot_iff (V₂.subgroupOf L)).mp hzero
      rw [hk] at hker
      intro v hv y hy
      exact congrArg Subtype.val (mem_center_iff.mp (hker (show
        (⟨v, hVL hv⟩ : L) ∈ V₂.subgroupOf L from hv)) ⟨y, c.y_le_component hy⟩)
    have hzeroV : V₂ = ⊥ := c.plane_two_commutator.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hVC)
    have hc := c.plane_two_card
    rw [Subgroup.card_eq_one.mpr hzeroV] at hc
    omega
  have hroot := Matrix.PSL3.LinearThree.BorelStructure.sylow_center_le_of_borel_invariant
    F (by omega : 0 < n) hF P W hWP hBW hWne
  have hcardV : Nat.card (V₂.subgroupOf L) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv).trans c.plane_two_card
  have hcardW : Nat.card W ≤ 4 := by
    have hd := (V₂.subgroupOf L).card_map_dvd f
    rw [hcardV] at hd
    exact Nat.le_of_dvd (by decide) hd
  have hbound : 2 ^ n ≤ 4 := by
    have hle := Nat.le_of_dvd (Nat.card_pos (α := W)) (card_dvd_of_le hroot)
    rw [card_map_of_injective (P : Subgroup PSL(3,F)).subtype_injective,
      Matrix.PSL3.LinearThree.card_center_sylow F (by omega : 0 < n) hF P] at hle
    exact hle.trans hcardW
  by_contra hne
  have hthree : 3 ≤ n := by omega
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hthree
  norm_num at hpow
  omega

/-- Cubic Borel rigidity gives the literal upstairs equality, including
the retained nontrivial central two-covers of PSL₃(4). -/
theorem linear_three_borel_centralizers
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {n : ℕ}
    (hn : 0 < n) (heven : Even n)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n))
    (hB : M ⊓ L = borel L S) :
    S ⊓ centralizer (Yplus : Set G) = S ⊓ centralizer (L : Set G) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : Theory.GroupTheory.IsQuasisimple L := by
    let := c.component.2
    exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe c.component_le)
  let f : L →* PSL(3,F) := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [modelMap_ker e, center_eq_twoCore c]
    exact pCore_isPGroup
  obtain ⟨T, hT⟩ := component_sylow c
  let P := T.mapSurjective hf
  have htheta : (theta (normalizer (T : Set L))).map L.subtype ≤ Yplus := by
    rw [theta_map_of_injective L.subtype L.subtype_injective,
      sylow_normalizer_map_subtype T hT, ← hB]
    exact (theta_mono (le_inf inf_le_left (inf_le_right.trans c.component_le))).trans
      c.theta_eq.le
  apply le_antisymm
  · rintro s ⟨hs, hsy⟩
    let si : normalizer (L : Set G) :=
      ⟨s, c.normalizes ((sylow_le_local c hs).2)⟩
    let a := L.normalizerMonoidHom si
    have ha : MulAut.centralQuotientAction e a = 1 := by
      apply Matrix.PSL3.LinearThree.CubicBorel.eq_one_of_fixes_sylowNormalizer_cubics
        hn heven hF P
      intro b hb hb3
      have hbt : b ∈ theta ((normalizer (T : Set L)).map f) := by
        rw [T.normalizer_map_surjective f hf]
        exact subset_closure ⟨hb, hb3⟩
      rw [← FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.theta_map_of_twoGroup_ker
        f hk] at hbt
      obtain ⟨x, hx, rfl⟩ := hbt
      change MulAut.centralQuotientAction e a (e (QuotientGroup.mk' (center L) x)) = _
      rw [MulAut.centralQuotientAction_apply]
      apply congrArg e
      apply congrArg (QuotientGroup.mk' (center L))
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr
        (hsy x (htheta (mem_map_of_mem L.subtype hx))).symm
    have ha1 : a = 1 := MulAut.centralQuotientAction_injective e
      (ha.trans (map_one _).symm)
    have hc : si ∈ L.normalizerMonoidHom.ker := ha1
    rw [normalizerMonoidHom_ker] at hc
    exact ⟨hs, hc⟩
  · exact inf_le_inf_left S (centralizer_le c.y_le_component)

theorem not_linear_three_borel
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {n : ℕ}
    (hn : 0 < n) (heven : Even n)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n))
    (hB : M ⊓ L = borel L S) : False :=
  centralizers_ne c (linear_three_borel_centralizers c hn heven hm hB)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
