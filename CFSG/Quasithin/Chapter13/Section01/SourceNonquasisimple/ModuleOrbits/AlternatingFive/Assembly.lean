module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.CentralCases.Source
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.OuterGeometry.Source
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.RadicalStabilizers.Source
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.CoreActions
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.SieveActions

/-!
# The complete natural A₅-cover branch of 13.1.12

For a locally Sylow-selected vector moved by T, the small-kernel and inner
exclusions force central rank two and a genuinely outer natural action.
The five-line quotient then identifies the original LT-image with S₅ and
gives the selected orbit lengths two and thirty. Its faithful kernel and
the trivial centralizer of A₅ in S₅ make O₂(XT) centralize U.

The component Sylow stabilizer lifts to Q₈ on the original odd Frattini
plane. These facts construct both OrbitFacts and SieveActions, with no
rank, outer-action, orbit or stabilizer premise. Only the genuine module
marking remains as the preceding classification input.

Source: Aschbacher--Smith 13.1.12, printed pp.872--874.
-/

public noncomputable section
open scoped Classical
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
open Chapter1 Chapter1.Section02 Chapter12.Section02
open SourceCentralizerStructure.Elimination
namespace Marking
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {L : Subgroup G} (d : Marking T L W)
include d

/-- The outer action is derived from the original selected noncentral point. -/
theorem source_outer_of_selected
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)) :
    Module.finrank (ZMod 2) d.projection.toLinearMap.ker = 2 ∧
      d.HasOuterNaturalAction := by
  obtain ⟨hd,t,ht⟩ := d.source_kernel_rank_two_and_outer h hL hn u hlocal hnt
  exact ⟨hd,fun hi => ht (hi t)⟩

/-- The actual S₅ action quotient, with kernel C_LT(U) and original L-image
A₅, is constructed under the original selected-point hypotheses. -/
theorem source_selected_outer_marking
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)) :
    Module.finrank (ZMod 2) d.projection.toLinearMap.ker = 2 ∧
      Nonempty (OuterMarking T L) := by
  obtain ⟨hd,ho⟩ := d.source_outer_of_selected h hL hn u hlocal hnt
  exact ⟨hd,⟨d.outerMarking (source_moved_commutator h hL hn) ho⟩⟩

/-- The selected noncentral row is the actual six-dimensional orthogonal
cover, equivariantly over the same natural projection. -/
theorem source_selected_orthogonal_equiv
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)) :
    ∃ (ζ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) CoverSpace)
      (e : CoverAction.Equiv d.representation),
      (∀ a l w, ζ a (CoverAction l w) = CoverAction (d.conjugation a l) (ζ a w)) ∧
      (∀ a w, CoverProjection (ζ a w) = d.naturalActor a (CoverProjection w)) ∧
      (∀ w, d.projection (e w) = CoverProjection w) ∧
      (∀ a w, e (ζ a w) = d.actor a (e w)) :=
  d.source_orthogonal_equiv h hL hn
    (d.source_outer_of_selected h hL hn u hlocal hnt).1

/-- The selected orbit formula on the literal LT, with its actual central
subspace condition. The small-kernel and inner cases are discharged. -/
theorem source_selected_orbit
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)) :
    (centralizer ({(u : G)} : Set G)).relIndex (L ⊔ (T : Subgroup G)) =
      if (u : G) ∈ centralizer (L : Set G) then 2 else 30 := by
  classical
  have ho := (d.source_outer_of_selected h hL hn u hlocal hnt).2
  have hi := d.selected_centralizer_index
    (d.outerMarking (source_moved_commutator h hL hn) ho) h hL hn u hlocal hnt
  simpa only [d.projection_zero_iff] using hi

/-- Source 13.1.12(2) in the A₅-cover row, including the T-central case. -/
theorem source_centralizer_index
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≤ 2 := by
  by_cases ht : (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)
  · rw [relIndex_eq_one.mpr ht]
    decide
  · exact (d.source_outer_orbit_and_stabilizer h hL hn
      (d.source_outer_of_selected h hL hn u hlocal ht).2 u hlocal).1

/-- The original radical action is irreducible at every nonidentity moved
vector, by transporting from the permitted selected representative. -/
theorem radical_irreducible {p : ℕ} [Fact p.Prime] (h : Context T L p)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    RadicalCentralizerIrreducible L p u := by
  apply radical_irreducible_of_selected h _ hu hne
  intro v s
  exact (d.source_radical_actions h.hypothesis h.maximal h.nonquasisimple
    h.odd h.divides ⟨v,s.mem⟩ s.local_sylow).1

/-- Source 13.1.12(1--2) together on the original locally selected vector. -/
theorem centralizer_index_and_radical_irreducible
    {p : ℕ} [Fact p.Prime] (h : Context T L p) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≤ 2 ∧
      RadicalCentralizerIrreducible L p u :=
  ⟨d.source_centralizer_index h.hypothesis h.maximal h.nonquasisimple u hlocal,
    (d.source_radical_actions h.hypothesis h.maximal h.nonquasisimple
      h.odd h.divides u hlocal).1⟩

/-- In the selected noncentral A₅ row the whole source two-core fixes U. -/
theorem source_core_centralizes {p : ℕ} [Fact p.Prime] (h : Context T L p)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G)) :
    (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (normalizerMoved L : Set G) := by
  have ho := (d.source_outer_of_selected h.hypothesis h.maximal h.nonquasisimple
    ⟨u,s.mem⟩ s.local_sylow hnt).2
  let q := d.outerMarking (source_moved_commutator h.hypothesis h.maximal h.nonquasisimple) ho
  exact radicalCore_centralizes_of_five_image h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides q.quotient q.kernel q.component

/-- All orbit and core-action premises of the centralizer consumer are
discharged for the genuine natural A₅-cover marking. -/
theorem orbitFacts {p : ℕ} [Fact p.Prime] (h : Context T L p) : OrbitFacts T L p where
  irreducible _ hu hne _ := d.radical_irreducible h hu hne
  index u s := d.source_centralizer_index h.hypothesis h.maximal h.nonquasisimple
    ⟨u,s.mem⟩ s.local_sylow
  core_action _ s hnt := inf_le_left.trans (d.source_core_centralizes h s hnt)

/-- The actual quaternion lifts discharge the two clauses of the sieve. -/
theorem sieveActions {p : ℕ} [Fact p.Prime] (h : Context T L p) : SieveActions h := by
  apply sieveActions_of_component_quaternions h
  intro u s _
  exact (d.source_radical_actions h.hypothesis h.maximal h.nonquasisimple
    h.odd h.divides ⟨u,s.mem⟩ s.local_sylow).2

/-- The literal fixed-core identity consumed by the pushing-up analysis. -/
theorem core_centralizer_eq {p : ℕ} [Fact p.Prime] (h : Context T L p)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G)) :
    centralizerCore T L p u =
      (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (normalizerMoved L : Set G) :=
  h.core_eq_fixed (d.orbitFacts h) s hnt

/-- The literal irreducible-component sieve application. Only the earlier
source control input remains, with the final source assembly owner. -/
theorem not_escape_of_irreducible {p : ℕ} [Fact p.Prime] (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) : False := by
  apply h.not_escape_of_sylow_irreducible (d.sieveActions h) c s hnt e hi
  apply h.sylow_radical_irreducible_of_quaternion
  apply sylow_quaternion_of_component_quaternion h u
  exact (d.source_radical_actions h.hypothesis h.maximal h.nonquasisimple
    h.odd h.divides ⟨u,s.mem⟩ s.local_sylow).2

end Marking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
