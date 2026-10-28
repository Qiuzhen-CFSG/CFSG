module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.ClassificationOrbits.ProductRows
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.ClassificationOrbits.SymmetricThree
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.SieveSymmetricThree

/-!
# Original moved-module classification, orbits and centralizer applications

All four source module rows supply radical irreducibility, the index bound
for locally Sylow-selected representatives, and the fixed-core identity on
the literal original subgroup U. Natural-three central covers are retained
through the product and irreducible source reductions, so the rank-four
branch uses its actual action and projection.

The quaternion rows supply the existing sieve actions. The deleted S5 row
supplies its actual S3 quotient directly to the complete component-model
exclusions. Thus the irreducible centralizer consumer has no extra module,
orbit, Sylow-action or classification premise. Existing public interfaces
remain available.

The primary 13.1.10 and 13.1.12(1--2) conclusions retain only the authorized
earlier Thompson movement, produced by qt-d-1317-supplements and discharged
by qt-d-1317-source. The later centralizer/TI consumers retain Control and
the independently owned reducible component-normalizer branch; their final
discharge belongs to qt-d-1317-source and its centralizer-sieve input.

Source: Aschbacher--Smith 13.1.10--14, printed pp.871--876.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 SourceCentralizerStructure.Elimination
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- Apply all source branches while retaining the actual natural covers.
The deleted S5 row retains its marking for the direct S3 sieve below. -/
theorem source_inputs_or_symmetric (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    (OrbitFacts T L p ∧ SieveActions h) ∨ Nonempty (SymmetricFiveRow T L) := by
  rcases reducedOffender_component_cases h.hypothesis h.many h.maximal
      h.nonquasisimple hmove with hd | hd | hd
  · exact quasisimple_inputs_or_symmetric h hmove hd.some
  · exact twoFactors_inputs_or_symmetric h hmove hd.some
  · exact Or.inl (hyperplane_centralizer_inputs h hmove hd.some)

/-- Source 13.1.12(1--2), together with the original fixed-core action:
all four module rows are discharged, assuming only earlier Thompson movement. -/
theorem orbitFacts_of_source (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    OrbitFacts T L p := by
  rcases source_inputs_or_symmetric h hmove with hi | hd
  · exact hi.1
  · exact hd.some.orbitFacts h

/-- The actual four-way module classification and every orbit/core input,
under only the original hypotheses and the earlier Thompson movement. -/
theorem classification_and_orbitFacts_of_source (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    Nonempty (FourWayMarking.{u,u} T L) ∧ OrbitFacts T L p :=
  ⟨fourWayMarking_of_source h.hypothesis h.many h.maximal h.nonquasisimple hmove,
    orbitFacts_of_source h hmove⟩

/-- Original 13.1.12(1) holds for every nonidentity moved vector, by
transporting its selected representative through the original normalizer. -/
theorem radical_irreducible_of_source (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    RadicalCentralizerIrreducible L p u :=
  radical_irreducible_of_selected h
    (fun _ s => h.selected_irreducible (orbitFacts_of_source h hmove) s) hu hne

/-- The literal two conclusions of 13.1.12, retaining the required local
Sylow choice for the index bound. No module marking is an extra premise. -/
theorem centralizer_irreducible_and_index_of_source
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1)
    (hs : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({u} : Set G))) :
    RadicalCentralizerIrreducible L p u ∧
      ((centralizer ({u} : Set G)).subgroupOf (T : Subgroup G)).index ≤ 2 := by
  let c : Context T L p := ⟨h,hmany,hL,hn,ho,hd⟩
  exact ⟨radical_irreducible_of_source c hmove hu hne,
    (orbitFacts_of_source c hmove).index u ⟨hu,hne,hs⟩⟩

/-- The fixed-core identity in the original pushing-up argument. Both
centralizers use the same O₂(XT), moved subgroup and selected vector. -/
theorem core_centralizer_eq_of_source (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G)) :
    centralizerCore T L p u =
      (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (normalizerMoved L : Set G) :=
  h.core_eq_fixed (orbitFacts_of_source h hmove) s hnt

/-- The symmetric-three half of the source sieve is discharged for every
module row on the literal odd Frattini action, without a marking premise. -/
theorem symmetricThreeQuotient_of_source_sylow_reducible (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    (hr : ¬ SylowRadicalIrreducible h u) : SymmetricThreeStabilizerQuotient L p u := by
  rcases source_inputs_or_symmetric h hmove with hi | hd
  · exact hi.2.symmetric_three u s hnt hr
  · exact hd.some.symmetricThreeStabilizerQuotient h s hnt

/-- Apply the completed source orbit analysis to the literal 13.1.13 TI
consumer. Only centralizer containment from 13.1.12(3) remains explicit;
its producer is the centralizer-sieve owner, with final discharge at source assembly. -/
theorem ti_of_source_and_selected_containment (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hc : ∀ u : G, Selected T L u →
      centralizer ({u} : Set G) ≤ normalizer (L : Set G)) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) :=
  h.ti_of_selected (orbitFacts_of_source h hmove) hc

/-- The same source inputs feed the original weak-closure consumer, with
only the independent 13.1.12(3) centralizer containment retained. -/
theorem weakClosure_of_source_and_selected_containment (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hc : ∀ u : G, Selected T L u →
      centralizer ({u} : Set G) ≤ normalizer (L : Set G)) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      (∀ i : ℕ, i ≤ 1 → ChapterE.indexedWeakClosure (normalizerMoved L) (T : Subgroup G) i ≤
        centralizer (normalizerMoved L : Set G)) ∧
      1 < ChapterE.globalW (normalizerMoved L) (T : Subgroup G) ∧
      1 < ChapterE.globalR (normalizerMoved L) := by
  apply normalizerMoved_weakClosure_of_centralizer_analysis h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides (orbitFacts_of_source h hmove).irreducible
  exact fun _ hu hne => h.centralizer_le_of_selected hc hu hne

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification


namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Subgroup Theory.GroupTheory
open Chapter1 Chapter1.Section02 SourceCentralizerStructure.Elimination
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The literal irreducible centralizer consumer, with every module-orbit
and action premise discharged from source. Earlier Control is owned by
qt-d-1317-source and its centralizer-sieve input. -/
theorem not_escape_of_irreducible_source_modules (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) : False := by
  rcases source_inputs_or_symmetric h hmove with hd | hd
  · exact h.not_escape_of_irreducible_source_actions hd.2 c s hnt e hi
  · exact not_escape_of_irreducible_symmetricThree h c s hnt e hi
      (hd.some.symmetricThreeStabilizerQuotient h s hnt)

/-- The final centralizer assembly needs only the separately owned reducible
component-normalizer branch and earlier Control. The module classification,
orbit inputs and entire irreducible branch are proved here. -/
theorem centralizer_le_of_source_reducible_exclusion (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (c : Control T L p)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) :=
  h.centralizer_le_of_component_exclusions (orbitFacts_of_source h hmove) c
    (fun _ s hnt _ e hi => not_escape_of_irreducible_source_modules h hmove c s hnt e hi)
    hred hu hne

/-- Literal 13.1.13 application after source orbit and irreducible assembly.
The reducible component branch and earlier Control retain their independent
producer qt-d-1317-centralizer-sieve, with final discharge at qt-d-1317-source. -/
theorem ti_of_source_reducible_exclusion (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (c : Control T L p)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) :=
  h.ti_of_component_exclusions (orbitFacts_of_source h hmove) c
    (fun _ s hnt _ e hi => not_escape_of_irreducible_source_modules h hmove c s hnt e hi)
    hred

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
