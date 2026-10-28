module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.FourGeneration.Certificate
public import Theory.Combinatorics.WalkClosure.RankContraction
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.FourGeneration.Certificate
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Generation

/-!
# Four-generation and the native Mathieu cycle base

The rank of an octad relative to the marked octad is read from their
intersection size. Checked words in the actual octad stabilizer reduce rank
comparisons to four representative vertices. Every horizontal edge has a
lower common neighbor. The lower neighbors of each representative have a
spanning tree whose edges are filled by squares entirely below that vertex.
Transporting those squares fills every two-edge peak. The general rank
contraction theorem then proves four-generation in the nonabelian normal
closure of closed walks.

Combined with the already proved triangle/square coplanarity and actual
local-edge orbit, this discharges the last premise of the native system's
cycle-base condition. No source group or local-comparison hypothesis is used.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 13.2(2–3),
printed p.210; compare 38.6–38.7, pp.207–208.
-/

section
noncomputable section
open Sporadic.Mathieu SimpleGraph SimpleGraph.WalkClosure
namespace Sporadic.Mathieu.M24LocalGeometry.OctadGraph
open PairOvergroups
open scoped Pointwise
namespace Descent
open DescentCertificate
def rank (O : Octad) : ℕ := rankSet O.val

def block (i : Fin 759) : Octad :=
  ⟨m24BlockAt i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

theorem rank_bound (O : Octad) : rank O ≤ 3 := by
  unfold rank rankSet
  split <;> omega

theorem rank_first : rank first = 0 := by decide +kernel

theorem rank_zero (O : Octad) (hO : rank O = 0) : O = first := by
  have hi : (O.val ∩ first.val).card = 8 := by
    unfold rank rankSet at hO
    split at hO <;> omega
  apply Subtype.ext
  have hcO := m24Blocks_card O.val O.property
  have hcf := m24Blocks_card first.val first.property
  have hiO : O.val ∩ first.val = O.val :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hif : O.val ∩ first.val = first.val :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  exact hiO.symm.trans hif

theorem rank_smul (g : M24) (hg : g • first = first) (O : Octad) :
    rank (g • O) = rank O := by
  have he : g • first.val = first.val := congrArg Subtype.val hg
  have hc : ((g • O).val ∩ first.val).card = (O.val ∩ first.val).card := by
    calc
      _ = (g • O.val ∩ g • first.val).card := by rw [he]; rfl
      _ = (g • (O.val ∩ first.val)).card := by rw [Finset.smul_finset_inter]
      _ = _ := Finset.card_smul_finset g _
  unfold rank rankSet
  rw [hc]

namespace PeakTools
section
variable (rank : Octad → ℕ)

def PeakBelow (x a b : Octad) : Prop :=
  ∃ (ha : graph.Adj a x) (hb : graph.Adj x b) (q : graph.Walk a b),
    (∀ v ∈ q.support, rank v < rank x) ∧
    Rel (shortCycles graph) (.cons ha (.cons hb .nil)) q

theorem peakBelow_refl {x a : Octad} (ha : graph.Adj x a) (hr : rank a < rank x) :
    PeakBelow rank x a a :=
  ⟨ha.symm, ha, .nil, by simpa using hr, spur ha.symm .nil⟩

theorem peakBelow_symm {x a b : Octad} (h : PeakBelow rank x a b) :
    PeakBelow rank x b a := by
  obtain ⟨ha,hb,q,hq,he⟩ := h
  refine ⟨hb.symm,ha.symm,q.reverse,?_,?_⟩
  · intro v hv
    exact hq v (by simpa using hv)
  · simpa only [Walk.reverse_cons, Walk.reverse_nil, Walk.nil_append, Walk.cons_append] using he.reverse

theorem peakBelow_trans {x a b c : Octad} (h : PeakBelow rank x a b)
    (h' : PeakBelow rank x b c) : PeakBelow rank x a c := by
  obtain ⟨ha,hb,q,hq,he⟩ := h
  obtain ⟨hb',hc,r,hr,he'⟩ := h'
  refine ⟨ha,hc,q.append r,?_,?_⟩
  · intro v hv
    rcases (Walk.mem_support_append_iff _ _).mp hv with hv | hv
    · exact hq v hv
    · exact hr v hv
  · have hh := (rel_cons ha (spur (S := shortCycles graph) hb (.cons hc .nil))).symm
    exact hh.trans (Rel.append he he')

theorem peakBelow_square {x a b c : Octad}
    (ha : graph.Adj a x) (hb : graph.Adj x b)
    (hac : graph.Adj a c) (hcb : graph.Adj c b)
    (hra : rank a < rank x) (hrb : rank b < rank x) (hrc : rank c < rank x) :
    PeakBelow rank x a b :=
  ⟨ha,hb,.cons hac (.cons hcb .nil), by simpa using And.intro hra (And.intro hrc hrb),
    short_paths _ _ (by simp)⟩

end
end PeakTools
open PeakTools

def representative (i : Fin 4) : Octad := block (representativeIndex i)

theorem root_transport (O : Octad) :
    ∃ (i : Fin 4) (g : M24), g • first = first ∧ g • representative i = O := by
  obtain ⟨b,_,hb⟩ := Finset.mem_image.mp O.property
  generalize hw : word b = w
  let g := LocalWords.evaluate w
  have hgen : ∀ j ∈ w, LocalWords.generator j ∈ MulAction.stabilizer M24 first := by
    intro j hj
    have hj' : j ∈ word b := by rw [hw]; exact hj
    exact LocalWords.vertexJoin_le (LocalWords.generator_vertexJoin j (word_fix b j hj'))
  have hg0 := LocalWords.evaluate_mem (MulAction.stabilizer M24 first) w hgen
  have hg : g ∈ MulAction.stabilizer M24 first := hg0
  refine ⟨label b,g,hg,?_⟩
  apply Subtype.ext
  change g • m24BlockAt (representativeIndex (label b)) = O.val
  rw [LocalWords.evaluate_smul]
  rw [← hw]
  exact (orbit_coverage b).trans hb

theorem representative_neighbor (i : Fin 4) (O : Octad) (hO : graph.Adj (representative i) O) :
    ∃ j : Fin 30, block (neighbor i j) = O := by
  obtain ⟨b,_,hb⟩ := Finset.mem_image.mp O.property
  have hc := neighbor_coverage i b (by rw [hb]; exact hO)
  refine ⟨neighborIndex i b,?_⟩
  rw [hc]
  exact Subtype.ext hb

theorem transported_neighbor (i : Fin 4) (g : M24) (O : Octad)
    (hO : graph.Adj (g • representative i) O) :
    ∃ j : Fin 30, g • block (neighbor i j) = O := by
  have hi : graph.Adj (representative i) (g⁻¹ • O) := by
    simpa only [inv_smul_smul] using preserves g⁻¹ hO
  obtain ⟨j,hj⟩ := representative_neighbor i (g⁻¹ • O) hi
  exact ⟨j, by rw [hj, smul_inv_smul]⟩

theorem descend (O : Octad) (hO : 0 < rank O) :
    ∃ P, rank P < rank O ∧ graph.Adj P O := by
  obtain ⟨i,g,hg,rfl⟩ := root_transport O
  have hi : 0 < rankSet (m24BlockAt (representativeIndex i)) := by
    rw [rank_smul g hg] at hO
    exact hO
  obtain ⟨ha,hr⟩ := down_valid i hi 0
  refine ⟨g • block (downNeighbor i 0),?_,preserves g ha.symm⟩
  rw [rank_smul g hg, rank_smul g hg]
  exact hr

theorem horizontal_lower (O P : Octad) (hOP : graph.Adj O P) (he : rank O = rank P) :
    ∃ Q, rank Q < rank O ∧ graph.Adj O Q ∧ graph.Adj Q P := by
  obtain ⟨i,g,hg,rfl⟩ := root_transport O
  obtain ⟨j,rfl⟩ := transported_neighbor i g P hOP
  have hr : rankSet (m24BlockAt (representativeIndex i)) =
      rankSet (m24BlockAt (neighbor i j)) := by
    rw [rank_smul g hg, rank_smul g hg] at he
    exact he
  obtain ⟨h1,h2,h3⟩ := horizontal_valid i j hr
  refine ⟨g • block (horizontal i j),?_,preserves g h1,preserves g h2⟩
  rw [rank_smul g hg, rank_smul g hg]
  exact h3

def lowerVertex (i : Fin 4) (g : M24) (j : Fin 15) : Octad :=
  g • block (downNeighbor i j)

theorem lowerVertex_adj (i : Fin 4) (g : M24)
    (hi : 0 < rankSet (m24BlockAt (representativeIndex i))) (j : Fin 15) :
    graph.Adj (g • representative i) (lowerVertex i g j) :=
  preserves g (down_valid i hi j).1

theorem lowerVertex_rank (i : Fin 4) (g : M24) (hg : g • first = first)
    (hi : 0 < rankSet (m24BlockAt (representativeIndex i))) (j : Fin 15) :
    rank (lowerVertex i g j) < rank (g • representative i) := by
  change rank (g • block (downNeighbor i j)) < rank (g • representative i)
  rw [rank_smul g hg, rank_smul g hg]
  exact (down_valid i hi j).2

theorem lowerVertex_peak (i : Fin 4) (g : M24) (hg : g • first = first)
    (hi : 0 < rankSet (m24BlockAt (representativeIndex i))) (j : Fin 15) :
    PeakBelow rank (g • representative i) (lowerVertex i g 0) (lowerVertex i g j) := by
  generalize hj : j.val = n
  induction n using Nat.strong_induction_on generalizing j with
  | h n ih =>
    rcases down_tree i hi j with he | ⟨hk,h1,h2,hr⟩
    · have he' : lowerVertex i g j = lowerVertex i g 0 := congrArg (fun k => g • block k) he
      rw [he']
      exact peakBelow_refl rank (lowerVertex_adj i g hi 0) (lowerVertex_rank i g hg hi 0)
    · have hp := ih (downParent i j).val (by omega) (downParent i j) rfl
      have hq : PeakBelow rank (g • representative i)
          (lowerVertex i g (downParent i j)) (lowerVertex i g j) := by
        apply peakBelow_square rank
          (lowerVertex_adj i g hi (downParent i j)).symm (lowerVertex_adj i g hi j)
          (preserves g (show graph.Adj (block (downNeighbor i (downParent i j)))
            (block (downCommon i j)) from h1))
          (preserves g (show graph.Adj (block (downCommon i j))
            (block (downNeighbor i j)) from h2))
          (lowerVertex_rank i g hg hi (downParent i j)) (lowerVertex_rank i g hg hi j)
        rw [rank_smul g hg, rank_smul g hg]
        exact hr
      exact peakBelow_trans rank hp hq

theorem peak_lower (A X B : Octad) (hAX : graph.Adj A X) (hXB : graph.Adj X B)
    (hA : rank A < rank X) (hB : rank B < rank X) :
    ∃ q : graph.Walk A B, (∀ v ∈ q.support, rank v < rank X) ∧
      Rel (shortCycles graph) (.cons hAX (.cons hXB .nil)) q := by
  obtain ⟨i,g,hg,rfl⟩ := root_transport X
  obtain ⟨a,rfl⟩ := transported_neighbor i g A hAX.symm
  obtain ⟨b,rfl⟩ := transported_neighbor i g B hXB
  have ha : rankSet (m24BlockAt (neighbor i a)) < rankSet (m24BlockAt (representativeIndex i)) := by
    rw [rank_smul g hg, rank_smul g hg] at hA
    exact hA
  have hb : rankSet (m24BlockAt (neighbor i b)) < rankSet (m24BlockAt (representativeIndex i)) := by
    rw [rank_smul g hg, rank_smul g hg] at hB
    exact hB
  have hi : 0 < rankSet (m24BlockAt (representativeIndex i)) := by omega
  have heA : lowerVertex i g (downIndex i a) = g • block (neighbor i a) :=
    congrArg (fun k => g • block k) (down_coverage i a ha)
  have heB : lowerVertex i g (downIndex i b) = g • block (neighbor i b) :=
    congrArg (fun k => g • block k) (down_coverage i b hb)
  have h := peakBelow_trans rank
    (peakBelow_symm rank (lowerVertex_peak i g hg hi (downIndex i a)))
    (lowerVertex_peak i g hg hi (downIndex i b))
  rw [heA,heB] at h
  obtain ⟨_,_,q,hq,he⟩ := h
  exact ⟨q,hq,he⟩

end Descent

/-- Exercise 13.2(2): the literal octad graph is generated by triangles,
squares, and backtracking in the nonabelian normal closure of closed walks. -/
public theorem fourGenerated : FourGenerated :=
  short_isCycleBase_of_rank Descent.rank first Descent.rank_first Descent.rank_zero
    Descent.descend Descent.horizontal_lower Descent.peak_lower 3 Descent.rank_bound

/-- The native local graph is a cycle base, with no remaining geometric premise. -/
public theorem system_isBase : system.IsBase := isBase_of_fourGenerated fourGenerated

end Sporadic.Mathieu.M24LocalGeometry.OctadGraph
