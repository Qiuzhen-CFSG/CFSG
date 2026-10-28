module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Contraction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.TripleLocalization
public import Theory.GroupTheory.Amalgam.UniquenessSystem.ShortCycles.Pentagons

/-!
# The normalized local pentagons in J₂ recognition

Squares already contract by the two source common-neighbor calculations.
A repeated vertex or chord from the first vertex reduces a pentagon to
triangles and squares. For the remaining loop, source 47.6(4) simultaneously
places its first vertex and opposite edge in C_G(z). Sylow conjugacy inside
that centralizer moves the first vertex exactly to X. Conjugation preserves
triangle homotopy, so only these normalized local configurations remain.

The common-neighbor move of 34.8 is also applied to the literal source
walks. The detailed mixed A₅/SL₂(3) and pure cases inside C_G(z), in the
rest of 47.9, are not assumed proved. Their contraction remains an explicit
premise, consumed by `ConcreteSystem.Recognition`.

Source: Aschbacher, *Sporadic Groups* (1994), 47.9, pp.265–266, using
34.6 and 34.8 and the completed source 47.6(4), 47.7 and 47.8.
-/

public section
open SimpleGraph.Walk SimpleGraph.Walk.TriangleHomotopy
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The common-neighbor configuration in the first case of source 47.9
contracts the actual five-step loop, using the proved source square criterion. -/
theorem pentagon_of_common_neighbor (D : Seed G) {A B C E F V : D.Vertex}
    (hab : D.graph.Adj A B) (hbc : D.graph.Adj B C) (hce : D.graph.Adj C E)
    (hef : D.graph.Adj E F) (hfa : D.graph.Adj F A)
    (hav : D.graph.Adj A V) (hcv : D.graph.Adj C V) (hev : D.graph.Adj E V) :
    TriangleHomotopy (.cons hab (.cons hbc (.cons hce (.cons hef hfa.toWalk)))) .nil :=
  SimpleGraph.pentagon_triangleHomotopy_of_common
    (CommonNeighbors.nonedge_connected D) hab hbc hce hef hfa hav hcv hev

/-- The only remaining source pentagons may be based at X with the opposite
edge inside the original C_G(z), with both endpoints distinct from and
nonadjacent to X. This retains every genuine local pentagon case of 47.9. -/
theorem triangleSimplyConnected_of_normalized_pentagons (D : Seed G)
    (hlocal : ∀ (A B C E : D.Vertex), B ≠ D.base → C ≠ D.base →
      ¬ D.graph.Adj D.base B → ¬ D.graph.Adj D.base C →
      B.val ≤ involutionCentralizer D.z → C.val ≤ involutionCentralizer D.z →
      ∀ (h0a : D.graph.Adj D.base A) (hab : D.graph.Adj A B)
        (hbc : D.graph.Adj B C) (hce : D.graph.Adj C E) (he0 : D.graph.Adj E D.base),
      TriangleHomotopy (.cons h0a (.cons hab (.cons hbc (.cons hce he0.toWalk)))) .nil) :
    D.graph.TriangleSimplyConnected := by
  have step {U A B C E : D.Vertex} (hua : D.graph.Adj U A) (hab : D.graph.Adj A B)
      (hbc : D.graph.Adj B C) (hce : D.graph.Adj C E) (heu : D.graph.Adj E U) :
      TriangleHomotopy (.cons hua (.cons hab (.cons hbc (.cons hce heu.toWalk)))) .nil := by
    apply SimpleGraph.pentagon_triangleHomotopy_of_nonadjacent
      (CommonNeighbors.nonedge_connected D) hua hab hbc hce heu
    intro hUB hUC hnB hnC
    obtain ⟨g, hg, hB, hC⟩ := TripleLocalization.normalize D B C U hbc
    have hne (T : D.Vertex) (hUT : U ≠ T) : g • T ≠ D.base := by
      intro he
      apply hUT
      exact (MulAction.toPerm g).injective (hg.trans he.symm)
    have hna (T : D.Vertex) (hUT : ¬ D.graph.Adj U T) :
        ¬ D.graph.Adj D.base (g • T) := by
      intro h
      apply hUT
      have hh := D.preserves g⁻¹ h
      rwa [← hg, inv_smul_smul, inv_smul_smul] at hh
    have huag : D.graph.Adj D.base (g • A) := by
      simpa only [hg] using D.preserves g hua
    have heug : D.graph.Adj (g • E) D.base := by
      simpa only [hg] using D.preserves g heu
    have hp := hlocal (g • A) (g • B) (g • C) (g • E)
      (hne B hUB) (hne C hUC) (hna B hnB) (hna C hnC) hB hC
      huag (D.preserves g hab) (D.preserves g hbc) (D.preserves g hce) heug
    let f : D.graph →g D.graph := ⟨fun T => g⁻¹ • T, fun h => D.preserves g⁻¹ h⟩
    have hi : g⁻¹ • D.base = U := by rw [← hg, inv_smul_smul]
    have hm := hp.map f
    simp only [map_cons, map_nil] at hm
    change TriangleHomotopy
      (.cons (D.preserves g⁻¹ huag) (.cons (D.preserves g⁻¹ (D.preserves g hab))
        (.cons (D.preserves g⁻¹ (D.preserves g hbc))
          (.cons (D.preserves g⁻¹ (D.preserves g hce))
            (D.preserves g⁻¹ heug).toWalk)))) .nil at hm
    convert! hm using 1 <;> congr! <;>
      first | exact hi.symm | exact (inv_smul_smul g _).symm
  apply triangleSimplyConnected_of_pentagons D
  intro U p hlen
  cases p with
  | nil => simp at hlen
  | @cons U A U hua p =>
    cases p with
    | nil => simp at hlen
    | @cons A B U hab p =>
      cases p with
      | nil => simp at hlen
      | @cons B C U hbc p =>
        cases p with
        | nil => simp at hlen
        | @cons C E U hce p =>
          cases p with
          | nil => simp at hlen
          | @cons E F U hef p =>
            cases p with
            | nil => exact step hua hab hbc hce hef
            | cons h p => simp at hlen

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
