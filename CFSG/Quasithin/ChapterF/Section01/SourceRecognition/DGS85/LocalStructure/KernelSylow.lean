module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Reduced
public import Theory.GroupTheory.AmalgamGraph.KernelSylow

/-!
# The actual vertex core is Sylow in the full local kernel

The reduced common Borel has its actual common Sylow normal. Normal-Sylow
control passes to its subgroups, in particular to each radius-one kernel.
The kernel core equals the vertex core, since the whole edge contains a
vertex Sylow. Transport uses the original conjugation and subtype maps.

This proves DGS (6.2)(d) at every vertex of the genuine reduced F1.11 graph,
without assuming the completion finite, identifying Q with U, or assuming
that the original S equals O₂(B). The full graph result states explicitly
the normality condition that the reduced application discharges.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, (6.2)(d), p.119, and the reduction on pp.95--96.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- DGS 6.2(d), from the literal edge and vertex Sylows. -/
theorem source_kernel_sylow (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (v : Vertex (family P)) :
    ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v := by
  let := finite_endpoints h
  have hbase (i : Bool) :
      ∃ T : Sylow 2 (U (family P) (base (family P) i)),
        (T : Subgroup (U (family P) (base (family P) i))).map
          (U (family P) (base (family P) i)).subtype = Q (family P) (base (family P) i) := by
    have hi : (graph (family P)).Adj (base (family P) i) (base (family P) (!i)) :=
      ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
    have hE : stabilizer (family P) (base (family P) i) ⊓
        stabilizer (family P) (base (family P) (!i)) = B := by
      rw [show stabilizer (family P) (base (family P) i) = family P i from
        Subgroup.CosetGeometry.stabilizer_base _ _,
        show stabilizer (family P) (base (family P) (!i)) = family P (!i) from
        Subgroup.CosetGeometry.stabilizer_base _ _]
      cases i
      · exact h.intersection
      · exact (inf_comm _ _).trans h.intersection
    have hSV : ∃ T : Sylow 2 (stabilizer (family P) (base (family P) i)),
        (T : Subgroup (stabilizer (family P) (base (family P) i))).map
          (stabilizer (family P) (base (family P) i)).subtype ≤ B := by
      rw [show stabilizer (family P) (base (family P) i) = family P i from
        Subgroup.CosetGeometry.stabilizer_base _ _]
      cases i
      · exact hS 0
      · exact hS 1
    obtain ⟨T, hT⟩ := hSV
    apply sylow_ballKernel_one (family P) hi (by rw [hE]; exact hB) T
    exact hT.trans (hE.ge.trans inf_le_right)
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
  have hu : U (family P) (base (family P) v.type) ≤
      stabilizer (family P) (base (family P) v.type) := U_le_stabilizer _ _
  let : Finite (U (family P) (base (family P) v.type)) :=
    Finite.of_injective (inclusion hu) (inclusion_injective _)
  rw [← hg, U_translate, Q_translate]
  exact sylow_witness_map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _ _ (hbase v.type)

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem parabolic_le_generated (i : Fin 2) : parabolic L S i ≤ generated L S := by
  rw [← parabolics_generate L S]
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

/-- Normality of the actual common Sylow makes the full Borel two-closed. -/
theorem f11_borel_core_sylow (h : HypothesisF11 L S)
    (hn : commonBorel L S ≤ normalizer (S : Set G)) :
    ∃ T : Sylow 2 (commonBorel L S),
      (T : Subgroup (commonBorel L S)) = pCore 2 (commonBorel L S) := by
  obtain ⟨T, hT⟩ := h.sylow_commonBorel
  refine ⟨T, le_antisymm ?_ (pCore_isPGroup.le_sylow_of_normal T)⟩
  have hc : S ≤ (commonBorel L S).pCoreIn 2 :=
    le_pCoreIn_of_normalizes h.S_isP le_sup_right hn
  intro x hx
  obtain ⟨y, hy, he⟩ := hc (hT ▸ mem_map_of_mem (commonBorel L S).subtype hx)
  exact (commonBorel L S).subtype_injective he ▸ hy

/-- The graph of the literal generated pair inherits its marked vertex Sylows. -/
theorem f11_generated_vertex_sylow (h : HypothesisF11 L S) (i : Fin 2) :
    ∃ T : Sylow 2 ((parabolic L S i).subgroupOf (generated L S)),
      (T : Subgroup ((parabolic L S i).subgroupOf (generated L S))).map
        ((parabolic L S i).subgroupOf (generated L S)).subtype ≤
          (commonBorel L S).subgroupOf (generated L S) := by
  let := h.finite_parabolic i
  obtain ⟨T, hT⟩ := h.sylow_parabolic i
  exact sylow_le_subgroupOf (parabolic L S i) (generated L S) (commonBorel L S)
    (parabolic_le_generated i) ⟨T, hT.le.trans le_sup_right⟩

/-- The original full graph satisfies 6.2(d) whenever its common Sylow is normal
in the full Borel; the reduced pair below discharges this condition. -/
theorem f11_kernel_sylow (h : HypothesisF11 L S)
    (hn : commonBorel L S ≤ normalizer (S : Set G)) (v : Vertex (fullFamily L S)) :
    ∃ T : Sylow 2 (U (fullFamily L S) v),
      (T : Subgroup (U (fullFamily L S) v)).map (U (fullFamily L S) v).subtype =
        Q (fullFamily L S) v := by
  let := h.finite_commonBorel
  have hBG : commonBorel L S ≤ generated L S :=
    (commonBorel_le_parabolic (L := L) (S := S) 0).trans (parabolic_le_generated 0)
  exact source_kernel_sylow h.generatedLocallyRankOneTriple
    (core_sylow_equiv (subgroupOfEquivOfLe hBG).symm (f11_borel_core_sylow h hn))
    (f11_generated_vertex_sylow h) v

namespace Reduction
/-- The entire reduced Borel has a normal Sylow, intrinsically in G₀. -/
theorem reduced_borel_core_sylow (h : HypothesisF11 L S) :
    ∃ T : Sylow 2 ((B₀ L S).subgroupOf (G₀ L S)),
      (T : Subgroup ((B₀ L S).subgroupOf (G₀ L S))) =
        pCore 2 ((B₀ L S).subgroupOf (G₀ L S)) := by
  let := h.finite_commonBorel
  let : Finite (B₀ L S) := Finite.of_injective (inclusion (B₀_le h)) (inclusion_injective _)
  have hc : ∃ T : Sylow 2 (B₀ L S), (T : Subgroup (B₀ L S)) = pCore 2 (B₀ L S) := by
    rw [B₀_eq_source h]
    apply f11_borel_core_sylow (SuzukiContainment.reduced_hypothesis h)
    exact (normal_subgroupOf_iff_le_normalizer
      (show SuzukiContainment.reducedSylow L S ≤ commonBorel L (SuzukiContainment.reducedSylow L S)
        from le_sup_right)).mp (SuzukiContainment.reduced_sylow_normal h)
  have hBG : B₀ L S ≤ G₀ L S :=
    (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left
  exact core_sylow_equiv (subgroupOfEquivOfLe hBG).symm hc

/-- The actual reduced endpoint Sylow is transported through the literal
inclusion into G₀, without changing the graph carrier by an equality cast. -/
theorem reduced_vertex_sylow (h : HypothesisF11 L S) (i : Fin 2) :
    ∃ T : Sylow 2 ((P₀ L S i).subgroupOf (G₀ L S)),
      (T : Subgroup ((P₀ L S i).subgroupOf (G₀ L S))).map
        ((P₀ L S i).subgroupOf (G₀ L S)).subtype ≤ (B₀ L S).subgroupOf (G₀ L S) := by
  let := h.finite_parabolic i
  let : Finite (P₀ L S i) := Finite.of_injective (inclusion (P₀_le h i)) (inclusion_injective _)
  have hP : P₀ L S i ≤ G₀ L S := by
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hT : ∃ T : Sylow 2 (P₀ L S i), (T : Subgroup (P₀ L S i)).map (P₀ L S i).subtype =
      SuzukiContainment.reducedSylow L S := by
    rw [P₀_eq_source h i]
    exact (SuzukiContainment.reduced_hypothesis h).sylow_parabolic i
  obtain ⟨T, hT⟩ := hT
  exact sylow_le_subgroupOf (P₀ L S i) (G₀ L S) (B₀ L S)
    hP ⟨T, hT.le.trans le_sup_right⟩

/-- Unconditional 6.2(d) for the genuine reduced F1.11 graph, with Q embedded
in the full local kernel U through its actual subtype map. -/
theorem reduced_kernel_sylow (h : HypothesisF11 L S)
    (v : Vertex (reducedFamily L S)) :
    ∃ T : Sylow 2 (U (reducedFamily L S) v),
      (T : Subgroup (U (reducedFamily L S) v)).map (U (reducedFamily L S) v).subtype =
        Q (reducedFamily L S) v :=
  source_kernel_sylow (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) v
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
