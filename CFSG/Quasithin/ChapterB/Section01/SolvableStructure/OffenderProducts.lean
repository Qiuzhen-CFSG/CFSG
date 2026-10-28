module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Factors
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Choices
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Classification
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Conjugation
public import Theory.Representation.BinaryOffender.Replacement
public import Theory.Representation.BinaryOffender.StableSaturation

/-!
# Offenders and stable families in concrete solvable FF factors

The concrete factors and their Sylow choices are imported directly, without
using the parent source-theorem assembly. At quadratic ratio one, every best
offender has weight equal to the dimension of the whole module. Consequently,
the proved offender-product classification shows that the equal-weight minimal
members are individual factor Sylow subgroups. It also gives the valid
first assertion of B.1.8(5): a stable family generates exactly the factors
whose Sylow subgroups occur in the family.

The proofs use the original `IsStable` definition. Equal-weight descent
selects each nontrivial coordinate, and conjugation supplies a generating
set for that factor. No equality of the family with its saturation is claimed.

The original lemmas with a classifier premise remain available. The final
results discharge that premise using `isBestOffender_iff_sylowProduct`.
`factorConjugation` and `factor_map_conj` give the ambient permutation of the
actual factors needed for B.1.12. All results remain conditional on the concrete
factor witness and, where required, ratio one; their existence under the source
solvability hypotheses belongs to the parent source-theorem assembly.

Source: Aschbacher–Smith, B.1.8(4)–(5), printed p. 70 (PDF p. 81), and
B.1.12, printed p. 73 (PDF p. 84).
-/

@[expose] public section

open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
  (d : SolvableFFFactors ρ)

/-- Ratio one rules out strict offenders by Thompson replacement. -/
theorem not_strong_of_ratio_eq_one (hq : quadraticRatio ρ = 1) : ¬ IsStrongFFModule ρ := by
  intro h
  have := (isStrongFFModule_iff_quadraticRatio_lt_one ρ).mp h
  simp [hq] at this

theorem best_weight_of_ratio_eq_one (hq : quadraticRatio ρ = 1)
    {A : Subgroup G} (hA : IsBestOffender ρ A) :
    weight ρ A = Module.finrank (ZMod 2) V := by
  have he := ((isBestOffender_iff_of_not_strong ρ
    (not_strong_of_ratio_eq_one hq) A).mp hA).2
  have hd := fixedCodim_add_finrank ρ A
  unfold weight
  omega

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- A consequence of the offender-product classification: an individual
factor Sylow subgroup is a best offender. -/
theorem factorSylow_best_of_classifier
    (hclass : ∀ A, IsBestOffender ρ A ↔ d.IsSylowProduct A)
    (i : Fin d.count) (S : Sylow 2 (d.factor i)) :
    IsBestOffender ρ (d.factorSylow i S) :=
  (hclass _).mpr (d.factorSylow_isSylowProduct i S)

/-- Equal-weight minimal best offenders are the individual factor Sylow
subgroups, conditional on the offender-product classification. -/
theorem minimal_iff_factorSylow_of_classifier (hq : quadraticRatio ρ = 1)
    (hclass : ∀ A, IsBestOffender ρ A ↔ d.IsSylowProduct A) (A : Subgroup G) :
    IsMinimalBestOffender ρ A ↔ ∃ (i : Fin d.count) (S : Sylow 2 (d.factor i)), A = d.factorSylow i S := by
  constructor
  · intro hA
    obtain ⟨choices, hc, ⟨i, hi⟩, he⟩ := (hclass A).mp hA.1
    obtain hbot | ⟨S, hS⟩ := hc i
    · exact (hi hbot).elim
    have hSA : d.factorSylow i S ≤ A := by rw [he, ← hS]; exact le_iSup choices i
    have hbest := d.factorSylow_best_of_classifier hclass i S
    refine ⟨i, S, (hA.2 _ hbest ⟨hSA, ?_⟩).symm⟩
    rw [best_weight_of_ratio_eq_one hq hbest, best_weight_of_ratio_eq_one hq hA.1]
  · rintro ⟨i, S, rfl⟩
    refine ⟨d.factorSylow_best_of_classifier hclass i S, fun B hB hBA => ?_⟩
    apply Subgroup.eq_of_le_of_card_ge hBA.1
    rw [d.factorSylow_card]
    have hne : Nat.card B ≠ 1 := fun h => hB.1.1 (Subgroup.card_eq_one.mp h)
    have hp := Nat.card_pos (α := B)
    omega

/-- The actual set of factors detected by the Sylow members of a family. -/
def stableFactorSet (P : Set (Subgroup G)) : Set (Fin d.count) :=
  {i | ∃ S : Sylow 2 (d.factor i), d.factorSylow i S ∈ P}

/-- The valid generated-factor assertion of B.1.8(5), conditional on (4).
Stability has precisely its existing definition; no saturation hypothesis is
used. -/
theorem stable_generatedBy_eq_of_classifier (hq : quadraticRatio ρ = 1)
    (hclass : ∀ A, IsBestOffender ρ A ↔ d.IsSylowProduct A)
    {P : Set (Subgroup G)} (hP : IsStable ρ P) :
    generatedBy P ⊤ = ⨆ i ∈ d.stableFactorSet P, d.factor i := by
  apply le_antisymm
  · refine iSup_le fun A => iSup_le fun hAP => ?_
    have hA := hP.2.1 A hAP.1
    obtain ⟨choices, hc, _, he⟩ := (hclass A).mp hA
    rw [he]
    refine iSup_le fun i => ?_
    rcases hc i with hbot | ⟨S, hS⟩
    · rw [hbot]
      exact bot_le
    · have hbest := d.factorSylow_best_of_classifier hclass i S
      have hle : d.factorSylow i S ≤ A := by rw [he, ← hS]; exact le_iSup choices i
      have hSP : d.factorSylow i S ∈ P := hP.2.2.2 A hAP.1 _ hbest.1
        ⟨hle, by rw [best_weight_of_ratio_eq_one hq hbest, best_weight_of_ratio_eq_one hq hA]⟩
      rw [hS]
      exact (d.factorSylow_le i S).trans
        (le_iSup_of_le i (le_iSup_of_le (show i ∈ d.stableFactorSet P from ⟨S, hSP⟩) le_rfl))
  · refine iSup_le fun i => iSup_le fun hi => ?_
    obtain ⟨S, hS⟩ := hi
    rw [← d.factorSylow_conjugates_generate i S]
    refine iSup_le fun g => ?_
    exact le_generatedBy_top_of_mem (hP.2.2.1 _ hS (g : G))

theorem stableFactorSet_nonempty_of_classifier (hq : quadraticRatio ρ = 1)
    (hclass : ∀ A, IsBestOffender ρ A ↔ d.IsSylowProduct A)
    {P : Set (Subgroup G)} (hP : IsStable ρ P) : (d.stableFactorSet P).Nonempty := by
  obtain ⟨A, hAP⟩ := hP.1
  have hA := hP.2.1 A hAP
  obtain ⟨choices, hc, ⟨i, hi⟩, he⟩ := (hclass A).mp hA
  rcases hc i with hbot | ⟨S, hS⟩
  · exact (hi hbot).elim
  have hbest := d.factorSylow_best_of_classifier hclass i S
  refine ⟨i, S, hP.2.2.2 A hAP _ hbest.1 ⟨?_, ?_⟩⟩
  · rw [he, ← hS]
    exact le_iSup choices i
  · rw [best_weight_of_ratio_eq_one hq hbest, best_weight_of_ratio_eq_one hq hA]

/-- Each actual factor Sylow subgroup is a best offender, using the proved
classification from the natural factor actions. -/
theorem factorSylow_best (hfaith : Function.Injective ρ) (hq : quadraticRatio ρ = 1)
    (i : Fin d.count) (S : Sylow 2 (d.factor i)) :
    IsBestOffender ρ (d.factorSylow i S) :=
  d.factorSylow_best_of_classifier (d.isBestOffender_iff_sylowProduct hfaith hq) i S

/-- Equal-weight minimal best offenders are precisely the Sylow two-subgroups
of individual factors, embedded in the ambient group. -/
theorem minimal_iff_factorSylow (hfaith : Function.Injective ρ)
    (hq : quadraticRatio ρ = 1) (A : Subgroup G) :
    IsMinimalBestOffender ρ A ↔
      ∃ (i : Fin d.count) (S : Sylow 2 (d.factor i)), A = d.factorSylow i S :=
  d.minimal_iff_factorSylow_of_classifier hq
    (d.isBestOffender_iff_sylowProduct hfaith hq) A

/-- The valid first assertion of B.1.8(5), with the selected factors specified
by the actual Sylow subgroups in the original stable family. -/
theorem stable_generatedBy_eq (hfaith : Function.Injective ρ)
    (hq : quadraticRatio ρ = 1) {P : Set (Subgroup G)} (hP : IsStable ρ P) :
    generatedBy P ⊤ = ⨆ i ∈ d.stableFactorSet P, d.factor i :=
  d.stable_generatedBy_eq_of_classifier hq
    (d.isBestOffender_iff_sylowProduct hfaith hq) hP

/-- A stable family selects at least one of the concrete factors. -/
theorem stableFactorSet_nonempty (hfaith : Function.Injective ρ)
    (hq : quadraticRatio ρ = 1) {P : Set (Subgroup G)} (hP : IsStable ρ P) :
    (d.stableFactorSet P).Nonempty :=
  d.stableFactorSet_nonempty_of_classifier hq
    (d.isBestOffender_iff_sylowProduct hfaith hq) hP

/-- The existential form of the generated-factor assertion, retaining
nonemptiness of the selected factor set. -/
theorem stable_generatedBy_eq_subproduct (hfaith : Function.Injective ρ)
    (hq : quadraticRatio ρ = 1) {P : Set (Subgroup G)} (hP : IsStable ρ P) :
    ∃ I : Set (Fin d.count), I.Nonempty ∧ generatedBy P ⊤ = ⨆ i ∈ I, d.factor i :=
  ⟨d.stableFactorSet P, d.stableFactorSet_nonempty hfaith hq hP,
    d.stable_generatedBy_eq hfaith hq hP⟩

end CFSG.Quasithin.ChapterB.SolvableFFFactors
