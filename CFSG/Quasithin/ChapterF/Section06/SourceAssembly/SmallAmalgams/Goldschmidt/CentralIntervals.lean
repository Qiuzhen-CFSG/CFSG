module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcGeneration
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackSetup
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.UniversalSetup
public import Theory.GroupAction.CubicTree.CentralIntervals
public import Theory.GroupAction.CubicTree.TrackFixer
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure

/-!
# The central intervals of Goldschmidt Section 6

The original finite local groups and the actual track construct the fixed
interval and a longest central interval for an edge-central involution.
The only earlier-source input is that this involution does not fix the whole
track, the precise conclusion supplied by (5.3). Endpoint noncommutation uses
the actual index-three stabilizers and the preceding short-arc generation.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.1)--(6.3),
printed pp.395--397.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- The finite fixed locus constructs the literal intervals; the hypothesis
that an edge-central involution moves a track vertex is the source (5.3) input. -/
theorem CubicTreeAction.exists_centralInterval (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (z : G) (hz : t.CentralInvolution z)
    (hmove : ∃ i, z • t.vertex i ≠ t.vertex i) : Nonempty (t.CentralInterval z) := by
  apply t.exists_centralInterval z hz.2
  rcases h.track_fixed_locus t {z} with hall | ⟨a, b, hab⟩
  · obtain ⟨i, hi⟩ := hmove
    have hmem : i ∈ t.toLine.fixedIndices {z} := by rw [hall]; trivial
    exact (hi (hmem z (Set.mem_singleton z))).elim
  · refine ⟨a, b, ?_⟩
    intro i
    have hm := Set.ext_iff.mp hab i
    simpa only [Line.fixedIndices, Set.mem_ofPred_eq, Set.mem_singleton_iff,
      forall_eq, Set.mem_Icc] using hm

/-- The literal earlier-source (5.3) premise, expressed using the shared fixer. -/
theorem CubicTreeAction.exists_centralInterval_of_not_mem_fixer (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (z : G) (hz : t.CentralInvolution z)
    (hnot : z ∉ t.fixer) : Nonempty (t.CentralInterval z) := by
  apply h.exists_centralInterval t z hz
  simpa only [Track.mem_fixer, not_forall] using hnot

private theorem centralizes_overgroup_of_mover {B H : Subgroup G} (_hBH : B ≤ H)
    (hindex : B.relIndex H = 3) {z x : G}
    (hB : ∀ b ∈ B, Commute z b) (hx : x ∈ H) (hxB : x ∉ B) (hzx : Commute z x) :
    ∀ a ∈ H, Commute z a := by
  let E := B.subgroupOf H
  let C := (centralizer ({z} : Set G)).subgroupOf H
  have hEC : E ≤ C := fun b hb => fun g hg => by
    have he : g = z := Set.mem_singleton_iff.mp hg
    subst g
    exact (hB b hb).eq
  have hE : E.index = 3 := hindex
  have hco := isCoatom_of_index_three E hE
  have hC : C = ⊤ := by
    rcases hco.le_iff.mp hEC with htop | heq
    · exact htop
    · have hxC : (⟨x, hx⟩ : H) ∈ C := fun g hg => by
        have he : g = z := Set.mem_singleton_iff.mp hg
        subst g
        exact hzx.eq
      rw [heq] at hxC
      exact (hxB hxC).elim
  intro a ha
  have haC : (⟨a, ha⟩ : H) ∈ C := by rw [hC]; trivial
  exact haC z (Set.mem_singleton z)

theorem CubicTreeAction.edge_vertex_relIndex (h : CubicTreeAction F)
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b) :
    (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b).relIndex
      (RankTwo.stabilizer F b) = 3 := by
  have hi := h.pathStabilizer_edge_index_three hab.symm
  have he : RankTwo.pathStabilizer F (show BasedWalk (RankTwo.graph F) 1 b from
      ⟨⟨a, hab.symm⟩, PUnit.unit⟩) =
        RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b := by
    ext g
    change (∀ v ∈ [b, a], g • v = v) ↔ g • a = a ∧ g • b = b
    simp [and_comm]
  rw [he] at hi
  exact hi

private theorem fixes_neighbor_of_centralizes {a b c : RankTwo.Vertex F} {z : G}
    (hab : (RankTwo.graph F).Adj a b) (hac : (RankTwo.graph F).Adj a c)
    (hzb : z • b = b) (hz : ∀ x ∈ RankTwo.stabilizer F a, Commute z x) :
    z • c = c := by
  obtain ⟨x, hx, hxbc⟩ := RankTwo.locally_transitive F hab hac
  rw [← hxbc, ← mul_smul, (hz x hx).eq, mul_smul, hzb]

/-- A mover at the right end of the central interval cannot commute with the
involution: otherwise it would extend the central interval by one edge. -/
theorem CubicTreeAction.not_commute_centralRight (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {z x : G} (d : t.CentralInterval z)
    (hx : x • t.vertex d.centralRight = t.vertex d.centralRight)
    (hxprev : x • t.vertex (d.centralRight - 1) ≠ t.vertex (d.centralRight - 1)) :
    ¬ Commute z x := by
  intro hzx
  have hlt := d.central_lt
  have hzedge := d.central (d.centralRight - 1) (by omega) (by omega)
  have hadj : (RankTwo.graph F).Adj (t.vertex (d.centralRight - 1))
      (t.vertex d.centralRight) := by
    simpa only [sub_add_cancel] using t.adjacent (d.centralRight - 1)
  have hzvertex : ∀ a ∈ RankTwo.stabilizer F (t.vertex d.centralRight), Commute z a := by
    apply centralizes_overgroup_of_mover (B := t.edgeStabilizer (d.centralRight - 1))
      (H := RankTwo.stabilizer F (t.vertex d.centralRight))
    · simpa only [Track.edgeStabilizer, sub_add_cancel] using
        (inf_le_right : RankTwo.stabilizer F (t.vertex (d.centralRight - 1)) ⊓
          RankTwo.stabilizer F (t.vertex d.centralRight) ≤ _)
    · simpa only [Track.edgeStabilizer, sub_add_cancel] using h.edge_vertex_relIndex hadj
    · exact hzedge.2
    · exact hx
    · exact fun hxE => hxprev hxE.1
    · exact hzx
  apply d.not_central_right
  refine ⟨⟨?_, ?_⟩, fun a ha => hzvertex a ha.1⟩
  · change z • t.vertex d.centralRight = t.vertex d.centralRight
    simpa only [sub_add_cancel] using hzedge.fixes_right
  · change z • t.vertex (d.centralRight + 1) = t.vertex (d.centralRight + 1)
    apply fixes_neighbor_of_centralizes hadj.symm (t.adjacent d.centralRight)
      hzedge.fixes_left hzvertex

theorem CubicTreeAction.not_commute_centralLeft (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {z x : G} (d : t.CentralInterval z)
    (hx : x • t.vertex d.centralLeft = t.vertex d.centralLeft)
    (hxnext : x • t.vertex (d.centralLeft + 1) ≠ t.vertex (d.centralLeft + 1)) :
    ¬ Commute z x := by
  apply h.not_commute_centralRight t.reverse d.reverse
  · simpa only [Track.CentralInterval.reverse, Track.reverse, neg_neg] using hx
  · have he : -(-d.centralLeft - 1) = d.centralLeft + 1 := by omega
    simpa only [Track.CentralInterval.reverse, Track.reverse, he] using hxnext

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
