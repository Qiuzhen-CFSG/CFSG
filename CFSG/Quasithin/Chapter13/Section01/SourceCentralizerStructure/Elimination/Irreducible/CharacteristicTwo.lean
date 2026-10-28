module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.CharacteristicTwo.OddModels
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.CharacteristicTwo.QuotientAction
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.Ordinary

/-!
# Excluding characteristic two under the original component model list

The odd row is excluded by the genuine C.2.7 star catalogue. In every even
linear-three row, C.2.7 bounds the center of K/O₂(K) by three, so the odd
complement embeds in its inner automorphism group. The original local actor,
radical containment and component Sylow supply all the inputs to the proved
quotient-action obstruction. Both SL₃ and PSL₃ covers are retained.

Together with the ordinary exclusion this eliminates every row of
IrreducibleComponentModels. Constructing that model list from the original
source hypotheses remains with qt-d-1317-centralizer-irreducible; the conditional
centralizer and TI consumers below do not assert that source sieve.
The earlier Control input remains with qt-d-1317-centralizer-sieve, and
OrbitFacts with qt-d-1317-module-orbits and its source assembly owner.
Source: Aschbacher–Smith, 13.1.12(3)–13, printed pp.874–875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.LinearThreeExclusion
open ChapterC.C27Source

/-- The actual characteristic-two branch has a faithful odd complement in
the inner group of K/O₂(K). The scalar-action argument excludes both even
linear-three covers, without replacing K by its quotient. -/
theorem Context.not_characteristic_two_even_linear_three (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hf : generalizedFitting K = pCore 2 K)
    {n : ℕ} (hn : 2 ≤ n) : ¬ LinearThreeModel (2^n) (XiQuotient K) := by
  intro hm
  have hc := coreQuotient_center_card_from_source
    (h.characteristic_two_input c s hnt e hi hf)
  have hz : Nat.Coprime p (Nat.card (center (XiQuotient K))) := by
    rcases hc with hc | hc
    · rw [hc]
      exact Nat.coprime_one_right p
    · rw [hc]
      exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (by decide) h.prime_gt_three)
  obtain ⟨F,_,_,hF,⟨j⟩⟩ := linearThree_center_model hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq := (RadicalConjugateRigidity.maximal_radical_structure
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides).1
  obtain ⟨S,_,hSX⟩ := h.component_sylow e
  exact core_quotient_linearThree_excluded F hn hF h.odd (XiP p L)
    (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) K
    (h.radical_le_local s) (XiP_invariant p inf_le_left)
    (h.local_normalizes_component s e hi) (h.radical_le_component s e hi)
    hq hi.local hz j S hSX

/-- The complete characteristic-two exclusion under the source model list.
The construction of that list remains with this task's model-sieve proof. -/
theorem Context.not_characteristic_two_of_models (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hm : IrreducibleComponentModels p K) :
    generalizedFitting K ≠ pCore 2 K := by
  intro hf
  rcases hm with hm | ⟨n,hn,_,_,hm⟩
  · exact h.not_characteristic_two_odd_linear_three c s hnt e hi hf hm
  · exact h.not_characteristic_two_even_linear_three c s hnt e hi hf hn hm

/-- Ordinary and characteristic-two exclusion discharge every model row.
This is conditional on the model list, not its source construction. -/
theorem Context.not_escape_of_models (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hm : IrreducibleComponentModels p K) : False :=
  h.not_characteristic_two_of_models c s hnt e hi hm
    (h.characteristic_two_of_models c s e hi hm)

/-- Literal centralizer containment after the source model sieve is supplied.
The reducible component-normalizer branch remains an independent input. -/
theorem Context.centralizer_le_of_irreducible_models (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p)
    (models : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        IrreducibleComponentModels p K)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  apply h.centralizer_le_of_component_exclusions o c _ hred hu hne
  intro v s hnt K e hi
  exact h.not_escape_of_models c s hnt e hi (models v s hnt K e hi)

/-- The actual TI application retains exactly the model sieve and the other
component branch; no characteristic-two exclusion callback remains. -/
theorem Context.ti_of_irreducible_models (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p)
    (models : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        IrreducibleComponentModels p K)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  apply h.ti_of_component_exclusions o c _ hred
  intro v s hnt K e hi
  exact h.not_escape_of_models c s hnt e hi (models v s hnt K e hi)

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
