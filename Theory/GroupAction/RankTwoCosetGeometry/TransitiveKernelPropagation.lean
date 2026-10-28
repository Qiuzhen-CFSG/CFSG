module
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon
/-!
# Propagating a relative normal subgroup to the third ball kernel

If a vertex stabilizer is transitive on nonbacktracking three-paths, a
subgroup it normalizes cannot fix the radius-two ball and the star of one
second vertex without fixing the radius-three ball. A shortest path to any
remaining vertex can be transported from the displayed path; relative
normality transports its fixed endpoint.

The DGS85 (12.9) application, printed p.189, uses the contrapositive for
the literal span W to exclude a torus from a second vertex's local kernel.
No tree or ambient finiteness assumption is used.
-/
public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)
/-- One second-vertex star constraint propagates a normalized radius-two subgroup. -/
theorem le_third_ballKernel_of_normalized_two_kernel {v : Vertex F}
    (ht : RootPathTransitive (graph F) G v 3)
    (p : BasedWalk (graph F) 3 v) (hp : p.Nonbacktracking)
    (N : Subgroup G) (hn : stabilizer F v ≤ normalizer (N : Set G))
    (hN : N ≤ ballKernel F v 2)
    (hNp : N ≤ ballKernel F (p.2.1 : Vertex F) 1) :
    N ≤ ballKernel F v 3 := by
  intro x hx z hz
  by_cases hz2 : z ∈ ball F v 2
  · exact hN hx z hz2
  have hdist : (graph F).edist v z ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp : ((3 : ℕ) : ℕ∞) ≠ ⊤) hz
  obtain ⟨w,hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top hdist
  have hlen : w.length = 3 := by
    have hlo : ¬ w.length ≤ 2 := by
      intro hh
      exact hz2 (hw.ge.trans (ENat.natCast_le_natCast.mpr hh))
    have hhi : w.length ≤ 3 := ENat.natCast_le_natCast.mp (hw ▸ hz)
    omega
  let q : BasedWalk (graph F) 3 v := hlen ▸ BasedWalk.ofWalk w
  have hqend : q.endpoint = z := by simp only [q,endpoint_cast,endpoint_ofWalk]
  have hgeo : (graph F).dist v z = 3 := by
    rw [SimpleGraph.dist,←hw,ENat.toNat_natCast,hlen]
  have hq : q.Nonbacktracking := nonbacktracking_of_geodesic q (hqend.symm ▸ hgeo)
  obtain ⟨g,hg,hgp⟩ := ht p q hp hq
  have hend : g • p.endpoint = z := by
    have hact : GraphAction (graph F) G :=
      ⟨fun g _ _ ha => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj ha⟩
    exact (endpoint_smul_of_vertices hact g p q hgp).trans hqend
  have hconj : g⁻¹*x*g ∈ N := by
    have hh := (mem_normalizer_iff.mp (hn ((stabilizer F v).inv_mem hg)) x).mp hx
    simpa only [inv_inv] using hh
  have hfix : (g⁻¹*x*g) • p.endpoint = p.endpoint := by
    apply hNp hconj
    exact (mem_ball_one F _ _).mpr (Or.inl p.2.2.1.property)
  apply (MulAction.injective g⁻¹)
  rw [←hend]
  simpa only [mul_smul,inv_smul_smul] using hfix
end Subgroup.CosetGeometry.RankTwo
