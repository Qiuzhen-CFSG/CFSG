module

public import Stellmacher.Recognition.LargeTerminalLocalCharacter
public import Stellmacher.Recognition.LargeTerminalFiveAction
public import Stellmacher.Recognition.LargeTerminalFiveFixedFour
public import Theory.GroupAction.IndexTwoFiveFixedPoints
public import Theory.GroupTheory.BinaryPowerFusion

/-!
# Local candidates for the large terminal transfer character

At the Sylow endpoint 4096, the local character detects an element of
fourth power one in the second local core, fixed by an actual subgroup of
order five. The five-subgroup fixes at most the order-two center in the
residual. Since that residual has index two in the local core, the fixed
subgroup in the core has order at most four. Orbit counting modulo five
makes its order exactly four, so it escapes the residual.

This supplies a bounded-order candidate for transfer from the actual
terminal structure in Stellmacher (10.1)(b). Ambient conjugacy of its
powers is a separate obligation; no fusion conclusion is assumed here.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup

universe u

/-- The local character detects a five-fixed element whose fourth power is one.
This theorem supplies the local candidate, without an ambient fusion assertion. -/
public theorem LargeTerminalContext.exists_local_transfer_candidate_fixed_center
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    ∃ (χ : S →* Multiplicative (ZMod 2)) (x : S) (A : Subgroup G),
      Nat.card A = 5 ∧
      A ≤ (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
        (ctx.first ⊔ ctx.second).subtype ∧
      A ≤ normalizer (ctx.firstResidual : Set G) ∧
      (x : G) ∈ centralizer (A : Set G) ∧
      (x : G) ∈ twoCoreIn ctx.second ∧ x ^ 4 = 1 ∧ χ x ≠ 1 ∧
      (∀ s : S, (s : G) ∈ twoCoreIn ctx.second →
        (χ s = 1 ↔ (s : G) ∈ ctx.firstResidual)) ∧
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
  obtain ⟨q, hqfixed, hqR, hqfour⟩ :=
    Theory.GroupAction.exists_fixed_pow_four_not_mem_of_index_two RQ hA hindex
      (by rw [hQcard]) hfixedcard
  obtain ⟨χ, hχ⟩ := ctx.exists_local_character hS
  let x : S := i q
  refine ⟨χ, x, A, hA, hAE, hAN, hcentral q hqfixed, q.property, ?_, ?_, hχ, hfixed⟩
  · change i q ^ 4 = 1
    rw [← map_pow, hqfour, map_one]
  · intro hx
    exact hqR ((hχ x q.property).mp hx)

/-- The local character detects a five-fixed element whose fourth power is one.
This theorem supplies the local candidate, without an ambient fusion assertion. -/
public theorem LargeTerminalContext.exists_local_transfer_candidate
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    ∃ (χ : S →* Multiplicative (ZMod 2)) (x : S) (A : Subgroup G),
      Nat.card A = 5 ∧
      A ≤ (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
        (ctx.first ⊔ ctx.second).subtype ∧
      A ≤ normalizer (ctx.firstResidual : Set G) ∧
      (x : G) ∈ centralizer (A : Set G) ∧
      (x : G) ∈ twoCoreIn ctx.second ∧ x ^ 4 = 1 ∧ χ x ≠ 1 ∧
      ∀ s : S, (s : G) ∈ twoCoreIn ctx.second →
        (χ s = 1 ↔ (s : G) ∈ ctx.firstResidual) := by
  obtain ⟨χ, x, A, hA, hAE, hAN, hxA, hxQ, hx4, hxχ, hχ, _⟩ :=
    ctx.exists_local_transfer_candidate_fixed_center hS
  exact ⟨χ, x, A, hA, hAE, hAN, hxA, hxQ, hx4, hxχ, hχ⟩

/-- The local character detects a five-fixed element whose fourth power is one
and whose square belongs to the Sylow omega-center. No ambient fusion is asserted. -/
public theorem LargeTerminalContext.exists_local_transfer_candidate_central_square
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    ∃ (χ : S →* Multiplicative (ZMod 2)) (x : S) (A : Subgroup G),
      Nat.card A = 5 ∧
      A ≤ (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
        (ctx.first ⊔ ctx.second).subtype ∧
      A ≤ normalizer (ctx.firstResidual : Set G) ∧
      (x : G) ∈ centralizer (A : Set G) ∧
      (x : G) ∈ twoCoreIn ctx.second ∧ x ^ 4 = 1 ∧ χ x ≠ 1 ∧
      (((x ^ 2) : S) : G) ∈ omegaOneCenter (S : Subgroup G) ∧
      ∀ s : S, (s : G) ∈ twoCoreIn ctx.second →
        (χ s = 1 ↔ (s : G) ∈ ctx.firstResidual) := by
  obtain ⟨χ, x, A, hA, hAE, hAN, hxA, hxQ, hx4, hxχ, hχ, hfixed⟩ :=
    ctx.exists_local_transfer_candidate_fixed_center hS
  refine ⟨χ, x, A, hA, hAE, hAN, hxA, hxQ, hx4, hxχ, ?_, hχ⟩
  have hsquare : χ (x ^ 2) = 1 := by
    rw [map_pow]
    have hc : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp
    simpa only [hc] using (pow_card_eq_one' (x := χ x))
  have hxQsq : (((x ^ 2) : S) : G) ∈ twoCoreIn ctx.second :=
    (twoCoreIn ctx.second).pow_mem hxQ 2
  have hxR := (hχ (x ^ 2) hxQsq).mp hsquare
  have hxAsq : (((x ^ 2) : S) : G) ∈ centralizer (A : Set G) :=
    (centralizer (A : Set G)).pow_mem hxA 2
  rw [← ctx.first_residual_center_eq_omegaOneCenter]
  exact mem_map.mpr ⟨⟨_, hxR⟩, hfixed hxAsq, rfl⟩

end Stellmacher.Recognition
