module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.ConcreteSystem.LocalGraph
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.ConcreteSystem.TriangleCertificate.Graph
public import Theory.GroupTheory.Amalgam.UniquenessSystem.TriangleBase

/-!
# A cycle base for the actual Hall–Janko uniqueness system

All eight common neighbors of the marked edge are enumerated. For each, a
word in the full pointwise edge fixer conjugates its cubic generator into
the literal local A₅. Both triangle types are therefore contained in translates
of the local graph. Together with the checked triangle contraction this proves
the target cycle-base premise of the universal-completion theorem.

Source: Aschbacher, *Sporadic Groups* (1994), §§34–37 and 47.10; the finite
word calculations use the unchanged ATLAS carrier and its existing provenance.
-/

public section
namespace CFSG.Quasithin.Janko23.J2Recognition.ConcreteSystem.TriangleCertificate
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.RecognitionGeometry
open Theory.GroupTheory
private def commonRow : Fin 8 → Fin 280 := ![13, 15, 19, 22, 27, 28, 264, 275]
private def edgeWord : Fin 8 → List (Fin 2) := ![[], [1], [], [0, 0, 0, 0, 1], [], [0, 0, 1], [0, 0, 0, 1], [0, 1]]
private def localWord : Fin 8 → List (Fin 3) := ![[2, 0, 1, 2, 0], [2, 0, 1, 2, 0], [1, 1, 0, 0], [1, 2, 0, 1], [0, 1, 0, 0], [1, 2, 0, 1], [1, 2, 0, 1], [1, 2, 0, 1]]
private def edgeModel (i : Fin 8) : alternatingGroup (Fin 5) :=
  evalWord LocalA5.EdgeData.model (edgeWord i)
private def localModel (i : Fin 8) : alternatingGroup (Fin 5) :=
  evalWord LocalA5.LocalData.model (localWord i)

private theorem triangle_checks : ∀ i p,
    OrbitAction.Data.value (commonRow i) (LocalA5.EdgeData.value (edgeModel i) p) =
      LocalA5.EdgeData.value (edgeModel i) (LocalA5.LocalData.value (localModel i) p) := by
  decide +kernel
open Subgroup

private theorem marked_third (i : Fin 8) :
    ∃ g : E, ((g : Carrier)⁻¹ • OrbitAction.vertex (commonRow i)).val ≤ K := by
  let g := LocalA5.edgeHom (edgeModel i)
  let l := LocalA5.localHom (localModel i)
  have hg : g ∈ E := by
    simpa only [LocalA5.edgeEquiv_symm_coe] using
      (LocalA5.edgeEquiv.symm (edgeModel i)).property
  have hl : l ∈ K := by
    simpa only [LocalA5.localEquiv_symm_coe] using
      (LocalA5.localEquiv.symm (localModel i)).property
  have he : OrbitAction.element (commonRow i) * g = g * l := by
    apply Sporadic.LeechRelated.J2.inclusion_injective
    apply Equiv.ext
    intro p
    simp only [map_mul, Equiv.Perm.mul_apply, g, l,
      OrbitAction.row_spec, LocalA5.edgeHom_value, LocalA5.localHom_value]
    exact triangle_checks i p
  refine ⟨⟨g, hg⟩, ?_⟩
  rw [smul_val, OrbitAction.vertex_val, MonoidHom.map_zpowers]
  apply zpowers_le.mpr
  change g⁻¹ * OrbitAction.element (commonRow i) * (g⁻¹)⁻¹ ∈ K
  rw [inv_inv, mul_assoc, he, ← mul_assoc, inv_mul_cancel, one_mul]
  exact hl

private theorem common_cases (i : Fin 280)
    (hi : RecognitionGeometry.TriangleCertificate.adjBool 0 i = true)
    (hj : RecognitionGeometry.TriangleCertificate.adjBool 4 i = true) :
    ∃ k, commonRow k = i := by
  have h : ∀ i : Fin 280,
      RecognitionGeometry.TriangleCertificate.adjBool 0 i = true →
      RecognitionGeometry.TriangleCertificate.adjBool 4 i = true → ∃ k, commonRow k = i := by
    decide +kernel
  exact h i hi hj

private theorem base_third (A : Vertex) (hA : graph.Adj base A)
    (hY : graph.Adj neighbor A) :
    ∃ g : E, ((g : Carrier)⁻¹ • A).val ≤ K := by
  obtain ⟨i, rfl⟩ := OrbitAction.vertex_surjective A
  have hzero : OrbitAction.vertex 0 = base := by
    simp only [OrbitAction.vertex, OrbitAction.rep_zero, inv_one, one_smul]
  have hfour : OrbitAction.vertex 4 = neighbor := OrbitAction.neighbor_zero
  obtain ⟨j, rfl⟩ := common_cases i
    ((RecognitionGeometry.TriangleCertificate.adjBool_iff 0 i).mpr (by simpa only [hzero] using hA))
    ((RecognitionGeometry.TriangleCertificate.adjBool_iff 4 i).mpr (by simpa only [hfour] using hY))
  exact marked_third j

/-- Both triangle types of the target graph lie in translates of the literal
local A₅ graph. The full eight-member common-neighbor set is checked. -/
theorem trianglesInLocalOrbits : system.TrianglesInLocalOrbits := by
  intro A B C hAB hBC hCA
  obtain ⟨g, hg⟩ := system.edge_transitive A B hAB
  rw [system_graph] at hAB hBC hCA
  have hpair : (g⁻¹ • A = base ∧ g⁻¹ • B = neighbor) ∨
      (g⁻¹ • A = neighbor ∧ g⁻¹ • B = base) := by
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [inv_smul_smul, system_base, system_neighbor] <;> tauto
  have hc : graph.Adj base (g⁻¹ • C) ∧ graph.Adj neighbor (g⁻¹ • C) := by
    rcases hpair with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact ⟨by simpa only [hA] using preserves g⁻¹ hCA.symm,
        by simpa only [hB] using preserves g⁻¹ hBC⟩
    · exact ⟨by simpa only [hB] using preserves g⁻¹ hBC,
        by simpa only [hA] using preserves g⁻¹ hCA.symm⟩
  obtain ⟨e, he⟩ := base_third (g⁻¹ • C) hc.1 hc.2
  have hef : (e : Carrier)⁻¹ ∈ Theory.GroupTheory.GraphUniquenessSystem.edgeFixer
      Carrier base neighbor := by
    rw [edgeFixer_eq]
    exact E.inv_mem e.property
  have hfx : (e : Carrier)⁻¹ • base = base := hef.1
  have hfy : (e : Carrier)⁻¹ • neighbor = neighbor := hef.2
  have hA : ((g * (e : Carrier))⁻¹ • A).val ≤ K := by
    rw [mul_inv_rev, mul_smul]
    rcases hpair with ⟨hA, _⟩ | ⟨hA, _⟩
    · rw [hA, hfx]
      exact le_sup_left.trans X_sup_Y_le_K
    · rw [hA, hfy]
      exact le_sup_right.trans X_sup_Y_le_K
  have hB : ((g * (e : Carrier))⁻¹ • B).val ≤ K := by
    rw [mul_inv_rev, mul_smul]
    rcases hpair with ⟨_, hB⟩ | ⟨_, hB⟩
    · rw [hB, hfy]
      exact le_sup_right.trans X_sup_Y_le_K
    · rw [hB, hfx]
      exact le_sup_left.trans X_sup_Y_le_K
  have hC : ((g * (e : Carrier))⁻¹ • C).val ≤ K := by
    simpa only [mul_inv_rev, mul_smul] using he
  exact ⟨g * e,
    (system_localEdge_iff _ _).mpr ⟨preserves _ hAB, hA, hB⟩,
    (system_localEdge_iff _ _).mpr ⟨preserves _ hBC, hB, hC⟩,
    (system_localEdge_iff _ _).mpr ⟨preserves _ hCA, hC, hA⟩⟩

/-- The actual target local graph is a cycle base. -/
theorem isBase : system.IsBase :=
  system.isBase_of_triangleSimplyConnected
    (by rw [system_graph]; exact RecognitionGeometry.TriangleCertificate.simplyConnected)
    trianglesInLocalOrbits

end CFSG.Quasithin.Janko23.J2Recognition.ConcreteSystem.TriangleCertificate
