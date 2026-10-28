module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairCoreGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicNoncommutingCatalogue
public import Theory.GroupAction.RankTwoCosetGeometry.ShortPaths

/-!
# Interior core control for strict noncommuting paths

The linear quotient supplied at every vertex of a strict noncommuting
profile lets the two-neighbor core lemma be applied at each turn of a
nonbacktracking path.  Consequently a two-subgroup fixing the path lies in
the actual two-core of every interior vertex.  This is the local core-control
input used when the six-path residual is compared with its seven-path
extensions in DGS (10.10).

The statement is deliberately phrased for the reduced completion.  It does
not identify the full path two-core with a residual, nor does it assert the
odd stabilizer conclusion; those are separate source steps.
-/

public noncomputable section
open Subgroup SimpleGraph Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open CFSG.Quasithin.ChapterF.Source.DGS85.Reduction

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S

/-- A two-subgroup fixing three consecutive vertices lies in the middle
vertex core.  The middle quotient is linear by the strict source catalogue. -/
theorem original_noncommuting_two_neighbor_core
    (h : HypothesisF11 L S) {v w : Vertex F}
    (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    {a m c : Vertex F} (ham : (graph F).Adj a m)
    (hmc : (graph F).Adj m c) (hac : a ≠ c)
    (A : Subgroup (G₀ L S)) (hp : IsPGroup 2 A)
    (hAa : A ≤ stabilizer F a) (hAm : A ≤ stabilizer F m)
    (hAc : A ≤ stabilizer F c) : A ≤ Q F m := by
  obtain ⟨n,hn,hm⟩ := reduced_noncommuting_actor_quotients_linear h hc hne m
  exact CommutingOneProfile.source_two_neighbor_two_group_le_core
    (reduced_triple h) (reduced_borel_core_sylow h)
    (reducedFullEarlierLocalTheorems h) ham hmc hac
    (.linear n hn hm) A hp hAa hAm hAc

/-- Every two-subgroup fixing a nonbacktracking path is contained in each
interior vertex core. -/
theorem original_noncommuting_path_two_subgroup_core
    (h : HypothesisF11 L S) {v w : Vertex F}
    (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    {r : ℕ} {a : Vertex F}
    (p : BasedWalk (graph F) (r+2) a) (hp : p.Nonbacktracking)
    (D : Subgroup (G₀ L S)) (hD : IsPGroup 2 D)
    (hfix : D ≤ pathStabilizer F p) :
    ∀ z ∈ p.2.vertices.dropLast, D ≤ Q F z := by
  induction r generalizing a with
  | zero =>
    rcases p with ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,q⟩⟩
    intro z hz
    have hzb : z = b := by
      simpa only [BasedWalk.vertices, List.dropLast_cons_cons,
        List.dropLast_singleton, List.mem_singleton] using hz
    subst z
    apply original_noncommuting_two_neighbor_core h hc hne hab hbc hp.1.symm D hD
    · intro d hd
      exact hfix hd a (by change a ∈ [a,b,c]; simp)
    · intro d hd
      exact hfix hd b (by change b ∈ [a,b,c]; simp)
    · intro d hd
      exact hfix hd c (by change c ∈ [a,b,c]; simp)
  | succ r ih =>
    rcases p with ⟨⟨b,hab⟩,q⟩
    have hq : D ≤ pathStabilizer F q := by
      intro d hd z hz
      exact hfix hd z (List.mem_cons_of_mem a hz)
    have hfirst : D ≤ Q F b := by
      apply original_noncommuting_two_neighbor_core h hc hne hab q.1.property hp.1.symm D hD
      · exact hfix.trans (pathStabilizer_le F _)
      · exact hq.trans (pathStabilizer_le F q)
      · intro d hd
        exact hq hd q.1.val (List.mem_cons_of_mem b (origin_mem_vertices F q.2))
    intro z hz
    have he : q.vertices.dropLast = b :: q.2.vertices.dropLast := by
      change (b :: q.2.vertices).dropLast = _
      exact List.dropLast_cons_of_ne_nil (List.ne_nil_of_mem (origin_mem_vertices F q.2))
    rw [he,List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hfirst
    · exact ih q hp.2 hq z hz

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
