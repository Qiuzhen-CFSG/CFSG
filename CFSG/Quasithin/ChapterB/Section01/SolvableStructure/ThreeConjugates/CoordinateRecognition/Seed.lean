module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.CoordinateInterface

/-!
# Selecting the cyclic-three coordinate

Stability at ratio one extracts each coordinate Sylow subgroup of a best
offender. The commutator identity then supplies one such subgroup acting
nontrivially on K. Since K lies in the normal stable generated subgroup,
its commutator with this Sylow lies in the corresponding factor and in K.
Order three forces K into that factor. This excludes diagonal support
without assuming ambient normality of individual factors or saturation
of the stable family.

Source: Aschbacher–Smith, B.1.12, printed p. 73 (PDF p. 84), the step
“we may take K⁺ = O(G₁⁺)”, using B.1.8(4) and Definition B.1.6.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ThreeConjugates
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem SolvableFFStructure.classifier (d : SolvableFFStructure ρ) (A : Subgroup G) :
    IsBestOffender ρ A ↔ d.toSolvableFFFactors.IsSylowProduct A := by
  classical
  rw [d.offender_product]
  constructor
  · rintro ⟨hne, B, hB, he⟩
    refine ⟨B, fun i => ?_, ?_, he⟩
    · rcases hB i with hb | ⟨S, hS⟩
      · exact Or.inl hb
      · exact Or.inr ⟨S, hS.symm⟩
    · by_contra hn
      push Not at hn
      apply hne
      rw [he]
      simp [hn]
  · rintro h
    refine ⟨h.ne_bot _, ?_⟩
    obtain ⟨B, hB, _, he⟩ := h
    refine ⟨B, fun i => ?_, he⟩
    rcases hB i with hb | ⟨S, hS⟩
    · exact Or.inl hb
    · exact Or.inr ⟨S, hS.symm⟩

theorem exists_active_factorSylow (d : SolvableFFStructure ρ)
    {P : Set (Subgroup G)} (hP : IsStable ρ P) {K S : Subgroup G}
    (hne : K ≠ ⊥) (hcomm : K = ⁅K, generatedBy P S⁆) :
    ∃ (i : Fin d.count) (R : Sylow 2 (d.factor i)),
      d.toSolvableFFFactors.factorSylow i R ∈ P ∧
      d.toSolvableFFFactors.factorSylow i R ≤ S ∧
      ⁅K, d.toSolvableFFFactors.factorSylow i R⁆ ≠ ⊥ := by
  classical
  by_contra hn
  push Not at hn
  have hcentral : generatedBy P S ≤ centralizer (K : Set G) := by
    refine iSup_le fun A => iSup_le fun hA => ?_
    have ha := hP.2.1 A hA.1
    obtain ⟨B, hB, _, he⟩ := (d.classifier A).mp ha
    rw [he]
    refine iSup_le fun i => ?_
    rcases hB i with hb | ⟨R, hR⟩
    · rw [hb]; exact bot_le
    have hRA : d.toSolvableFFFactors.factorSylow i R ≤ A := by
      rw [he, ← hR]; exact le_iSup B i
    have hbest := d.toSolvableFFFactors.factorSylow_best_of_classifier d.classifier i R
    have hRP := hP.2.2.2 A hA.1 _ hbest.1
      ⟨hRA, by rw [SolvableFFFactors.best_weight_of_ratio_eq_one d.ratio_one hbest,
        SolvableFFFactors.best_weight_of_ratio_eq_one d.ratio_one ha]⟩
    rw [hR]
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (hn i R hRP (hRA.trans hA.2)))
  apply hne
  rw [hcomm]
  exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcentral)

omit [FiniteDimensional (ZMod 2) V] in
theorem three_le_factor_of_active (d : SolvableFFStructure ρ)
    {P : Set (Subgroup G)} (hP : IsStable ρ P) {K S : Subgroup G}
    (hcard : Nat.card K = 3) (hcomm : K = ⁅K, generatedBy P S⁆)
    (i : Fin d.count) (R : Sylow 2 (d.factor i))
    (hRP : d.toSolvableFFFactors.factorSylow i R ∈ P)
    (hRS : d.toSolvableFFFactors.factorSylow i R ≤ S)
    (hactive : ⁅K, d.toSolvableFFFactors.factorSylow i R⁆ ≠ ⊥) :
    K ≤ d.factor i := by
  let J := generatedBy P ⊤
  let : J.Normal := hP.generatedBy_normal ρ
  have hlocal : generatedBy P S ≤ J :=
    iSup_le fun A => iSup_le fun hA => le_generatedBy_top_of_mem hA.1
  have hKJ : K ≤ J := by
    rw [hcomm]
    exact (commutator_mono le_rfl hlocal).trans (commutator_le_right _ _)
  have hJ : J ≤ offenderSubgroup ρ :=
    iSup_le fun A => iSup_le fun hA =>
      le_iSup_of_le A (le_iSup_of_le ⟨hP.2.1 A hA.1, le_top⟩ le_rfl)
  have hnorm : K ≤ normalizer (d.factor i) :=
    (hKJ.trans hJ).trans ((normal_subgroupOf_iff_le_normalizer
      (d.toSolvableFFFactors.factor_le_offenderSubgroup i)).mp
        (d.toSolvableFFFactors.factor_normal_in_offenderSubgroup i))
  have hCF : ⁅K, d.toSolvableFFFactors.factorSylow i R⁆ ≤ d.factor i :=
    (commutator_mono le_rfl (d.toSolvableFFFactors.factorSylow_le i R)).trans
      (le_normalizer_iff_commutator_le_right.mp hnorm)
  have hCK : ⁅K, d.toSolvableFFFactors.factorSylow i R⁆ ≤ K := by
    calc
      _ ≤ ⁅K, generatedBy P S⁆ := commutator_mono le_rfl
        (le_iSup_of_le _ (le_iSup_of_le ⟨hRP, hRS⟩ le_rfl))
      _ = K := hcomm.symm
  have hcdiv := card_dvd_of_le hCK
  rw [hcard] at hcdiv
  have hceq : Nat.card ↥(⁅K, d.toSolvableFFFactors.factorSylow i R⁆ : Subgroup G) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hcdiv).resolve_left
      (fun h => hactive (card_eq_one.mp h))
  have he : ⁅K, d.toSolvableFFFactors.factorSylow i R⁆ = K :=
    eq_of_le_of_card_ge hCK (by rw [hcard, hceq])
  exact he ▸ hCF

/-- Stability supplies a coordinate Sylow acting nontrivially on K. Its
commutator lies in both K and that factor; order three forces containment. -/
theorem exists_three_coordinate (d : SolvableFFStructure ρ)
    {P : Set (Subgroup G)} (hP : IsStable ρ P) {K S : Subgroup G}
    (hcard : Nat.card K = 3) (hcomm : K = ⁅K, generatedBy P S⁆) :
    ∃ i : Fin d.count, K ≤ d.factor i ∧
      i ∈ d.toSolvableFFFactors.stableFactorSet P := by
  have hne : K ≠ ⊥ := by intro h; rw [h, card_bot] at hcard; omega
  obtain ⟨i, R, hRP, hRS, ha⟩ := exists_active_factorSylow d hP hne hcomm
  exact ⟨i, three_le_factor_of_active d hP hcard hcomm i R hRP hRS ha, R, hRP⟩
end CFSG.Quasithin.ChapterB.ThreeConjugates
