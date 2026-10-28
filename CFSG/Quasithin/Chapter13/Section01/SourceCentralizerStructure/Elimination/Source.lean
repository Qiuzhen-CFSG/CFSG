module

public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.SourceControl
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.Source
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped

/-!
# Original involution-centralizer containment and its TI application

For the canonical radical X = Ξ_p(L), starred membership gives the unique
maximal two-local over XT. The source module classification supplies the
selected-representative orbits and point-core action, so SourceControl
constructs the actual pushing-up setup in C_G(u). An escaping C-component
would have either irreducible or reducible relative normalizer action;
the two completed component exclusions rule out both possibilities.
Transport through N_G(L) gives containment for every nonidentity element
of U = normalizerMoved L, and the literal 13.1.13 consumer gives TI.

The only earlier source premises retained here are X ∈ Ξ*(G,T), produced
by qt-d-1314-canonical-radical-star, and L = [L,J(T)], produced by
qt-d-1317-supplements. Their final discharge belongs to qt-d-1317-source.
No orbit, model, component-exclusion or pushing-up premise remains. The
maximal-counterexample application uses these same earlier premises at
the actual chosen faithful maximal subgroup.

Source: Aschbacher--Smith, 13.1.4(4), 13.1.9(2), and 13.1.12--14,
printed pp.867, 869--876. The final application is to original 13.3.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter12.Section02 SourceNonquasisimple
open SourceNonquasisimple.ModuleOrbits
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- Original 13.1.12(3), conditional only on the earlier starred-radical
and Thompson-movement statements. All local control and both component
branches are constructed, and the representative choice is discharged. -/
theorem Context.centralizer_le_of_radical_star (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hx : XiP p L ∈ XiStar G (T : Subgroup G))
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  have o := Classification.orbitFacts_of_source h hmove
  have c := h.control_of_radical_star o hx
  apply h.centralizer_le_of_source_irreducible hmove c _ hu hne
  intro v s hnt K e hr
  exact h.swapped_false o c s hnt e hr

/-- All three clauses of original 13.1.12 at a locally Sylow-selected
representative, on the original radical action and point centralizer. -/
theorem Context.centralizer_analysis_of_radical_star (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hx : XiP p L ∈ XiStar G (T : Subgroup G))
    {u : G} (s : Selected T L u) :
    RadicalCentralizerIrreducible L p u ∧
      ((centralizer ({u} : Set G)).subgroupOf (T : Subgroup G)).index ≤ 2 ∧
      centralizer ({u} : Set G) ≤ normalizer (L : Set G) :=
  ⟨Classification.radical_irreducible_of_source h hmove s.mem s.ne_one,
    (Classification.orbitFacts_of_source h hmove).index u s,
    h.centralizer_le_of_radical_star hmove hx s.mem s.ne_one⟩

/-- Original 13.1.13: the completed containment theorem supplies the
literal TI consumer, with the full normalizer equality retained. -/
theorem Context.ti_of_radical_star (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hx : XiP p L ∈ XiStar G (T : Subgroup G)) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  apply normalizerMoved_ti_of_centralizer_analysis h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides
    (Classification.orbitFacts_of_source h hmove).irreducible
  exact fun _ hu hne => h.centralizer_le_of_radical_star hmove hx hu hne

/-- The TI and weak-closure consequences needed by the terminal 13.1.7
argument, with both original centralizer-analysis inputs discharged. -/
theorem Context.weakClosure_of_radical_star (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hx : XiP p L ∈ XiStar G (T : Subgroup G)) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      (∀ i : ℕ, i ≤ 1 → ChapterE.indexedWeakClosure (normalizerMoved L) (T : Subgroup G) i ≤
        centralizer (normalizerMoved L : Set G)) ∧
      1 < ChapterE.globalW (normalizerMoved L) (T : Subgroup G) ∧
      1 < ChapterE.globalR (normalizerMoved L) := by
  apply normalizerMoved_weakClosure_of_centralizer_analysis h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides
    (Classification.orbitFacts_of_source h hmove).irreducible
  exact fun _ hu hne => h.centralizer_le_of_radical_star hmove hx hu hne

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceNonquasisimple
open Chapter13.Section01.SourceCentralizerStructure.Elimination
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- Apply the completed centralizer sieve to the actual maximal
nonquasisimple counterexample in 13.3.2. The two hypotheses are precisely
the earlier source statements owned by qt-d-1317-supplements and
qt-d-1314-canonical-radical-star; qt-d-1317-source discharges them. -/
theorem Hypothesis1331.nonquasisimple_ti_counterexample_of_radical_star
    (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn0 : ¬ IsQuasisimple (XiQuotient L₀))
    (hmove : ∀ K : Subgroup G, L₀ ≤ K → FaithfulMaximalLocal T K →
      ¬ IsQuasisimple (XiQuotient K) → K = ⁅K, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hstars : ∀ K : Subgroup G, L₀ ≤ K → FaithfulMaximalLocal T K →
      ¬ IsQuasisimple (XiQuotient K) →
      ∀ (p : ℕ) [Fact p.Prime], Odd p →
        p ∣ Nat.card (fittingSubgroup (XiQuotient K)) →
        XiP p K ∈ XiStar G (T : Subgroup G)) :
    ∃ K : Subgroup G, L₀ ≤ K ∧ FaithfulMaximalLocal T K ∧
      ¬ IsQuasisimple (XiQuotient K) ∧
      IsElementaryAbelian 2 (normalizerMoved K) ∧
      ⁅normalizerMoved K,K⁆ = normalizerMoved K ∧
      8 ≤ Nat.card (normalizerMoved K) ∧
      normalizer (normalizerMoved K : Set G) = normalizer (K : Set G) ∧
      IsTISubgroup (normalizerMoved K) ∧
      (∀ i : ℕ, i ≤ 1 → ChapterE.indexedWeakClosure (normalizerMoved K) (T : Subgroup G) i ≤
        centralizer (normalizerMoved K : Set G)) ∧
      1 < ChapterE.globalW (normalizerMoved K) (T : Subgroup G) ∧
      1 < ChapterE.globalR (normalizerMoved K) := by
  apply h.nonquasisimple_ti_counterexample_of_many hmany hn0
  intro K hLK hK hn p hp ho hd u hu hne
  let c : Context T K p := ⟨h.hypothesis1311,hmany,hK,hn,ho,hd⟩
  have hm := hmove K hLK hK hn
  exact ⟨fun _ => ModuleOrbits.Classification.radical_irreducible_of_source c hm hu hne,
    c.centralizer_le_of_radical_star hm (hstars K hLK hK hn p ho hd) hu hne⟩

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
