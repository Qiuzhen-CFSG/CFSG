module

public import Stellmacher.Recognition.LargeTerminalLocalCharacterData
public import Stellmacher.Recognition.LargeTerminalFiveAction
public import Theory.GroupAction.IndexTwoFiveFixedPoints

/-!
# The actual order-four fixed subgroup at the upper terminal endpoint

The original order-five subgroup fixes exactly four elements in the second
local core when the prescribed Sylow has order 4096. Its fixed subgroup in
the index-two first residual lies in that residual's center of order two.
Orbit counting modulo five gives the exact fixed order.

This retains the literal ambient embeddings for the later fusion argument.
Source: Stellmacher (10.1)(18)--(20) and Thompson VI, pp.629--630.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup

universe u

/-- The residual center is the omega-center of the prescribed ambient Sylow. -/
public theorem LargeTerminalContext.first_residual_center_eq_omegaOneCenter
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    CenterAmbient ctx.firstResidual = omegaOneCenter (S : Subgroup G) := by
  rw [ctx.first_residual_structure.2.1]
  have hn := (lemma_seven_five ctx.terminal.sectionSeven ctx.terminal.Γ
    ctx.terminal.criticalPath ctx.commuting).next_center.1
  change ZAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep =
    omegaOneCenter ((S : Subgroup G).subgroupOf (ctx.first ⊔ ctx.second)) at hn
  rw [hn]
  have hm := omegaOneCenterAmbient_map_injective
    (ctx.first ⊔ ctx.second).subtype (ctx.first ⊔ ctx.second).subtype_injective
    ((S : Subgroup G).subgroupOf (ctx.first ⊔ ctx.second))
  rw [map_subgroupOf_eq_of_le ctx.terminal.sylow_le_join] at hm
  exact hm.symm

/-- The original order-five subgroup fixes exactly four elements in the
actual order-1024 core. Cyclicity of this fixed subgroup is a separate assertion. -/
public theorem LargeTerminalContext.exists_five_fixed_four_of_large_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    ∃ A : Subgroup G, Nat.card A = 5 ∧ A ≤ ctx.second ∧
      A ≤ normalizer (ctx.firstResidual : Set G) ∧
      Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4 ∧
      (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤ center ctx.firstResidual := by
  let Q := twoCoreIn ctx.second
  let R := ctx.firstResidual
  have hSP : (S : Subgroup G) ≤ ctx.second :=
    ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  have hQS : Q ≤ (S : Subgroup G) := by
    rintro x ⟨q, hq, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
      (S.subtype hSP) hq
  obtain ⟨_, _, _, hlow, hhigh, _⟩ := ctx.involution_centralizer_core
  have hRQ : R ≤ Q := hlow.trans hhigh
  have hRcard : Nat.card R = 512 := ctx.first_residual_structure.1
  have hQcard : Nat.card Q = 1024 := by
    have h := ctx.local_character_core_card hS
    rw [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv] at h
    exact h
  let RQ := R.subgroupOf Q
  let RS := R.subgroupOf (S : Subgroup G)
  let _ : RS.Normal := ctx.local_character_residual_normal
  let i : Q →* S := inclusion hQS
  have hnormal : RQ.Normal := (inferInstance : RS.Normal).comap i
  let _ := hnormal
  have hindex : RQ.index = 2 := by
    have h := RQ.index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hRQ).toEquiv, hRcard, hQcard] at h
    omega
  obtain ⟨A, hA, hAE, hAN, hfixed⟩ := ctx.exists_five_subgroup_fixed_center
  have hAP : A ≤ ctx.second := by
    have hEP : EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep ≤
        GAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep := by
      rw [show EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep =
        twoResidualIn (GAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep) from
          ctx.terminal.Γ.twoResidualAt_def _]
      exact twoResidualIn_le _
    have hmap := (nine_two_ambient_setup
      (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext).2.2.1
    exact hAE.trans ((map_mono hEP).trans_eq hmap)
  have hPQ : ctx.second ≤ normalizer (Q : Set G) := by
    have h := (pCore 2 ctx.second).le_normalizer_map ctx.second.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  let _ : MulDistribMulAction A Q := conjMulDistribMulActionOfLeNormalizer A Q (hAP.trans hPQ)
  have hcentral (q : Q) (hq : q ∈ FixedPoints.subgroup A Q) :
      (q : G) ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    have hh := congrArg Subtype.val (hq ⟨a, ha⟩)
    change a * (q : G) * a⁻¹ = (q : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hfixedcard : Nat.card ((FixedPoints.subgroup A Q).subgroupOf RQ) ≤ 2 := by
    let f : ((FixedPoints.subgroup A Q).subgroupOf RQ) → center R := fun q =>
      ⟨⟨q.1.1, q.1.2⟩, hfixed (hcentral q.1.1 q.2)⟩
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (Subtype.ext (Subtype.ext
        (congrArg (fun z : center R => ((z : R) : G)) h)))
    exact (Nat.card_le_card_of_injective f hf).trans_eq ctx.first_residual_structure.2.2.2.1
  have hcard := Theory.GroupAction.fixed_card_four_of_index_two RQ hA hindex
    (by rw [hQcard]) hfixedcard
  have heq : FixedPoints.subgroup A Q = (centralizer (A : Set G)).subgroupOf Q := by
    ext q
    constructor
    · exact hcentral q
    · intro hq a
      apply Subtype.ext
      change (a : G) * (q : G) * (a : G)⁻¹ = (q : G)
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hq a a.property)
  exact ⟨A, hA, hAP, hAN, heq ▸ hcard, hfixed⟩


end Stellmacher.Recognition
