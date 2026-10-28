module

public import Stellmacher.SectionFiveToSeven.Result7_3
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction

/-!
# Local inputs for Stellmacher (7.8)

The hypotheses of (7.8), with any Sylow 2-subgroup of the edge stabilizer,
give the local-family, normality, and actor inputs for primitive extraction.
The neighboring 2-core is normal in and contained in that Sylow subgroup;
the neighboring center is likewise normal there. The actor lies in this
normal core and has an element outside the other vertex's 2-core.

The proof uses the edge transport established in (7.3), containment of a
normal 2-subgroup in every Sylow 2-subgroup, and restriction of normality.
No containment of the neighboring center in the other vertex's 2-core is
asserted: the subgroup-orbit assembly does not require that stronger claim.

Source: Journal of Algebra 190 (1997), (7.8), p. 36, applying (3.6).
The source-facing numbered statements are not changed here.
-/

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u

/-- The precise local data used to extract the dihedral configuration at an edge. -/
public structure SevenEightLocalInputs
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Gamma : CosetGraphContext G S P1 P2) (d l : Gamma.Vertex)
    (A : Subgroup G)
    (T : Sylow 2 ↥(stabilizer Gamma d ⊓ stabilizer Gamma l)) : Prop where
  sectionThree : Stellmacher.SectionThree.Hypotheses G
    (sylowTwoAmbient (stabilizer Gamma d ⊓ stabilizer Gamma l) T)
  first_mem : stabilizer Gamma d ∈ Stellmacher.SectionThree.PSet ⊤
    (sylowTwoAmbient (stabilizer Gamma d ⊓ stabilizer Gamma l) T)
  second_mem : stabilizer Gamma l ∈ Stellmacher.SectionThree.PSet ⊤
    (sylowTwoAmbient (stabilizer Gamma d ⊓ stabilizer Gamma l) T)
  solvable : Group.IsSolvable (stabilizer Gamma d)
  edge_generated : stabilizer Gamma d ⊔ stabilizer Gamma l = ⊤
  neighbor_core_normal : NormalIn (q Gamma l)
    (sylowTwoAmbient (stabilizer Gamma d ⊓ stabilizer Gamma l) T)
  neighbor_center_normal : NormalIn (z Gamma l)
    (sylowTwoAmbient (stabilizer Gamma d ⊓ stabilizer Gamma l) T)
  actor_le : A ≤ sylowTwoAmbient (stabilizer Gamma d ⊓ stabilizer Gamma l) T
  frattini_le_core : frattiniAmbient A ≤ twoCoreAmbient (stabilizer Gamma d)
  outside_actor : ∃ a, a ∈ A ∧ a ∉ twoCoreAmbient (stabilizer Gamma d)

private theorem normalIn_restrict
    {G : Type u} [Group G] {N W P : Subgroup G}
    (hN : NormalIn N P) (hNW : N ≤ W) (hWP : W ≤ P) : NormalIn N W := by
  refine ⟨hNW, (Subgroup.normal_subgroupOf_iff_le_normalizer hNW).mpr ?_⟩
  exact hWP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hN.1).mp hN.2)

/-- Every edge Sylow subgroup supports primitive extraction under the exact
actor and Frattini hypotheses of (7.8). -/
public theorem sevenEight_local_inputs
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2)
    (d l : Gamma.Vertex) (hl : l ∈ neighborhood Gamma d)
    (A : Subgroup G) (hA : A ≤ q Gamma l)
    (hAnot : ¬ A ≤ q Gamma d)
    (hPhi : frattiniAmbient A ≤ q Gamma d)
    (T : Sylow 2 ↥(stabilizer Gamma d ⊓ stabilizer Gamma l)) :
    SevenEightLocalInputs Gamma d l A T := by
  classical
  let W := sylowTwoAmbient (stabilizer Gamma d ⊓ stabilizer Gamma l) T
  obtain ⟨h3, hd, hlP, hsolv, hgen, hzNormal⟩ := edge_sectionThree_data h Gamma hl T
  have hWP : W ≤ stabilizer Gamma l :=
    Stellmacher.SectionThree.sylow_le_of_mem_PSet hlP
  have hqW : q Gamma l ≤ W := by
    obtain ⟨U, hU⟩ := hlP.1.2.1
    change (U : Subgroup (stabilizer Gamma l)).map (stabilizer Gamma l).subtype = W at hU
    rw [q, Gamma.twoCoreAt_def, twoCoreIn, ← hU]
    exact Subgroup.map_mono ((pCore_isPGroup (p := 2)).le_sylow_of_normal U)
  have hqNormal : NormalIn (q Gamma l) (stabilizer Gamma l) := by
    rw [q, Gamma.twoCoreAt_def]
    refine ⟨Subgroup.map_subtype_le _, ?_⟩
    change (((pCore 2 (stabilizer Gamma l)).map
      (stabilizer Gamma l).subtype).subgroupOf (stabilizer Gamma l)).Normal
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hdl : d ∈ neighborhood Gamma l := by
    rw [neighborhood, Gamma.neighbors_def] at hl ⊢
    change Gamma.distance d l = 1
    change Gamma.distance l d = 1 at hl
    exact (Gamma.distance_symm d l).trans hl
  have hzq : z Gamma l ≤ q Gamma l :=
    ((lemma_seven_three h Gamma).center_core l d hdl).trans
      ((Subgroup.map_mono (Subgroup.map_subtype_le _)).trans
        (Subgroup.map_subtype_le _))
  have hcore : q Gamma d = twoCoreAmbient (stabilizer Gamma d) := by
    rw [q, Gamma.twoCoreAt_def]
    rfl
  refine ⟨h3, hd, hlP, hsolv, hgen,
    normalIn_restrict hqNormal hqW hWP,
    normalIn_restrict hzNormal (hzq.trans hqW) hWP,
    hA.trans hqW, hcore ▸ hPhi, ?_⟩
  by_contra hnone
  apply hAnot
  intro a ha
  by_contra hnot
  exact hnone ⟨a, ha, by simpa only [← hcore] using hnot⟩

end Stellmacher.SectionsFiveToSeven

