module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.ModelPruning.Groups
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.SmallQuotients
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.BinarySylow

/-!
# Excluding the odd-prime swapped component through its actual star model

The genuine pushing-up input supplies the B.5.1 group-family list for the
literal star image. The existing star-kernel equality identifies that image
with the component's two-core quotient. If this quotient is PSL₂(q) for an
odd prime q, the proved group-model comparisons leave only orders 60 and 168.
The original canonical plane excludes both small orders. This closes the
odd-prime branch without the full C.2.7 geometric classification.

The final theorem combines the odd and even branches for the original
PushingUpComponent and Configuration. Their characteristic-normalizer
control remains a genuine earlier-source premise, not a model callback.
Source: Aschbacher–Smith, 1.3.8, printed pp.513–514, and C.2.7, pp.145–147.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open XiEmbedding FullSieve
open Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases
open ChapterC.C27Source

variable {Q : Type*} [Group Q] [Finite Q]

theorem starModel_odd_prime_small_card (h : StarModels.Model Q)
    {q : ℕ} (hq : q.Prime) (ho : Odd q) (hm : ClassicalGroup.IsPSL Q 2 q) :
    Nat.card Q = 60 ∨ Nat.card Q = 168 := by
  have hs : SwappedModel 3 Q := Or.inr ⟨q,hq,ho,hm⟩
  cases h with
  | linearTwo F e =>
    have hb : ClassicalGroup.IsPSL Q 2 (2^F.degree) :=
      ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,
        ⟨e.trans (Representation.SL2NaturalH1.projectiveEquiv (K := F.Carrier)).symm⟩⟩
    obtain ⟨he,_⟩ := even_psl_odd_prime_overlap hb hq ho hm
    have hc := even_psl_order hb
    rw [he] at hc
    exact Or.inl (by norm_num at hc ⊢; exact hc)
  | linearThree F e =>
    obtain ⟨_,he⟩ := slThree_odd_prime_parameters (by have := F.degree_pos; omega)
      F.card_eq e hq ho hm
    have hc := (psl_order hm).2
    rw [he] at hc
    exact Or.inr (by norm_num at hc ⊢; omega)
  | symplectic F _ e => exact (SourceAssembly.ModelPruning.not_symplectic F e hs).elim
  | g2 F _ e => exact (SourceAssembly.ModelPruning.not_g2 F e hs).elim
  | g2DerivedTwo e => exact (not_binaryG2Derived_quotient hs ⟨e⟩).elim
  | alternating n hn e =>
    have hlo : 5 ≤ n := by rcases hn with rfl | rfl | rfl | rfl <;> decide
    have hhi : n ≤ 8 := by rcases hn with rfl | rfl | rfl | rfl <;> decide
    obtain rfl := alternating_degree hlo hhi ⟨e⟩ hs
    exact Or.inl (by rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]; norm_num)
  | linearFiveTwo e =>
    exact (SourceAssembly.ModelPruning.not_binaryLinear (Or.inr rfl) e hs).elim
  | tripleSix z e => exact (SourceAssembly.ModelPruning.not_tripleSix z e hs).elim

variable {G : Type*} [Group G] [Finite G]

theorem source_odd_prime_small_card {H R M K : Subgroup G}
    (h : FullSieve.SourceInterface.Input KnownSimple.IsKnownSimple H R M K)
    {q : ℕ} (hq : q.Prime) (ho : Odd q)
    (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 q) :
    Nat.card (XiQuotient K) = 60 ∨ Nat.card (XiQuotient K) = 168 := by
  have hs : SwappedModel 3 (XiQuotient K) := Or.inr ⟨q,hq,ho,hm⟩
  let e := coreStarEquivOfSwapped h.normalizes h.quasisimple
    (kernel_offender_from_source h).1.upper hs
  have hmstar : ClassicalGroup.IsPSL (starImage K R K) 2 q :=
    hm.of_mulEquiv e.symm
  have hc := starModel_odd_prime_small_card (star_model_from_source h) hq ho hmstar
  simpa only [Nat.card_congr e.toEquiv] using hc

theorem PushingUpComponent.false_of_odd_swapped_of_large
    {p : ℕ} {T X P M H K : Subgroup G}
    (h : PushingUpComponent KnownSimple.IsKnownSimple p T X P M H K)
    (hp : 3 < p) (hs : SwappedFactors T P K)
    (hm : ∃ q : ℕ, q.Prime ∧ Odd q ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 q) :
    False := by
  obtain ⟨q,hq,ho,hmodel⟩ := hm
  have hc := source_odd_prime_small_card
    (FullSieve.SourceInterface.input_of_pushingUpComponent h) hq ho hmodel
  have hn := h.toComponentCandidate.not_small_quotient_card hp hs
    (Or.inr ⟨q,hq,ho,hmodel⟩)
  exact hc.elim hn.1 hn.2

theorem PushingUpComponent.false_of_odd_swapped
    {p : ℕ} {T X P L M H K : Subgroup G}
    (h : PushingUpComponent KnownSimple.IsKnownSimple p T X P M H K)
    (hc : Configuration p T X P L M) (hs : SwappedFactors T P K)
    (hm : ∃ q : ℕ, q.Prime ∧ Odd q ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 q) :
    False := h.false_of_odd_swapped_of_large hc.large hs hm

/-- Both literal swapped-model alternatives contradict the original pushing-up configuration. -/
theorem PushingUpComponent.false_of_swapped
    (T : Sylow 2 G) {p : ℕ} {X P L M H K : Subgroup G}
    (h : PushingUpComponent KnownSimple.IsKnownSimple p T X P M H K)
    (hc : Configuration p T X P L M)
    (h114 : HOver G (T : Set G) ⊆ He G)
    (hs : SwappedFactors T P K) (hm : SwappedModel p (XiQuotient K)) : False := by
  rcases hm with heven | hodd
  · exact h.false_of_even_swapped T hc h114 hs heven
  · exact h.false_of_odd_swapped hc hs hodd

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
