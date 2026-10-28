module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralFixedRegular
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralVertexAction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralCommutator
public import Theory.GroupAction.CubicTree.CentralReflection
public import Theory.GroupAction.CubicTree.OddIntervalReflections

/-!
# Reduction of an odd fixed interval to radii one and two

An odd regular fixed interval is shorter than the first singular length.
Symmetry about a central vertex rules out a two-edge central block, so the
block is one edge and the two margins are equal. Preferred-track reflections
then align both interval boundaries, giving the commutator bound at most two.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.5), pp.397–398.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon Theory.GroupTheory
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.odd_centralInterval_unit_block_and_equal_margins
    (h : CubicTreeAction F) {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z) (ho : Odd (d.fixedRight-d.fixedLeft)) :
    d.centralRight = d.centralLeft + 1 ∧ d.leftMargin = d.rightMargin := by
  have hlen := h.odd_centralInterval_length_lt_singularity (by omega) hshort p hp hn t d ho
  have hwidth := h.centralInterval_length_le_two hs hshort t hz d
  have hlt := d.central_lt
  have he : d.centralRight = d.centralLeft + 1 := by
    by_contra hne
    have htwo : d.centralRight = d.centralLeft + 2 := by omega
    let c := d.centralLeft + 1
    have hc := h.centralizes_vertex_of_two_centralEdges (by omega) hshort t c
      (d.central (c-1) (by dsimp[c]; omega) (by dsimp[c]; omega))
      (d.central c (by dsimp[c]; omega) (by dsimp[c]; omega))
    have hcwithin : d.fixedLeft ≤ c ∧ c ≤ d.fixedRight := by
      have hl := d.centralLeft_mem
      have hr := d.centralRight_mem
      dsimp [c]
      omega
    have he := h.centralInterval_symmetric_of_centralVertex hshort t d c hlen hcwithin hc
    obtain ⟨j, hj⟩ := ho
    omega
  refine ⟨he, ?_⟩
  have hc := h.central_margin_comparison hs hshort t hz hz d d
  have hl := d.leftMargin_cast
  have hr := d.rightMargin_cast
  obtain ⟨j, hj⟩ := ho
  omega

theorem CubicTreeAction.odd_centralInterval_rightMargin_le_two
    (h : CubicTreeAction F) {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G)
    (hfinite : ∀u,t.CentralInvolution u→u∉t.fixer)
    (hpreferred : AdjacentInvolutionMovers (RankTwo.graph F) G → t.HasReflections)
    {z : G} (hz : t.CentralInvolution z) (d : t.CentralInterval z)
    (ho : Odd (d.fixedRight-d.fixedLeft)) : d.rightMargin ≤ 2 := by
  obtain ⟨hw, hm⟩ := h.odd_centralInterval_unit_block_and_equal_margins hs hshort p hp hn t hz d ho
  have href := Track.hasReflections_of_odd_centralInterval hpreferred d hz ho
  obtain ⟨z', hz', d', halign, halign'⟩ := d.exists_double_aligned hz href hw hm
  exact h.double_boundary_rightMargin_le_two hs hshort hC hA t hfinite hz hz' d d' halign halign'

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
