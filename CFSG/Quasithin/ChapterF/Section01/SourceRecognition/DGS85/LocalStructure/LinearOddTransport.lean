module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearMarking
public import Theory.SpecificGroups.SL2.OddBorelTransversal
public import Theory.GroupTheory.AmalgamGraph.LinearPathKernel

/-!
# Odd-order transport in the actual linear local action

The original local quotient is adjusted by an inner automorphism so its
Borel preimage is the literal neighbor stabilizer. An odd-order matrix
coset representative then lifts to an odd-order element of the original
local group. Local transitivity supplies its target orbit. The quotient
version uses the proved equality of the local-group core and the vertex
core; it does not replace that core by the full permutation kernel.

The reduced F1.11 application constructs the local quotient from the original
PSL₂ marking, including F₂, and retains the actual action on the coset graph.

Source: DGS, Groups and Graphs (1985), 6.5, printed p.122.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Odd-order transport with the actual quotient kernel and neighbor stabilizer. -/
theorem source_linear_odd_neighbor_transport (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w z : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hvz : (graph (family P)).Adj v z)
    (q : graphLocalGroup (family P) v →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = (Q (family P) v).subgroupOf (graphLocalGroup (family P) v)) :
    ∃ x ∈ graphLocalGroup (family P) v, Odd (orderOf x) ∧ x • w = z := by
  let := finite_endpoints h
  let J := graphLocalGroup (family P) v
  let : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨a,ha⟩ := source_linear_borel_marking h hB hS hvw q hq hk
  let q' := (MulAut.conj a).toMonoidHom.comp q
  have hb : MulAction.stabilizer J w = (Matrix.SpecialLinearGroup.rankOneBorel F).comap q' := ha
  obtain ⟨g,hg,hgz⟩ := graphLocalGroup_transitive h hB hS v ⟨w,hvw⟩ ⟨z,hvz⟩
  obtain ⟨x,hx,hxz⟩ := Matrix.SpecialLinearGroup.exists_odd_mover_of_borel_stabilizer
    q' ((MulAut.conj a).surjective.comp hq) w z hb ⟨⟨g,hg⟩,hgz⟩
  refine ⟨x,x.property,?_,hxz⟩
  change Odd (orderOf (J.subtype x))
  rw [orderOf_injective J.subtype J.subtype_injective x]
  exact hx

/-- The intrinsic core quotient supplies the literal action-kernel marking. -/
theorem source_linear_odd_neighbor_transport_of_quotient (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w z : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hvz : (graph (family P)).Adj v z)
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    ∃ x ∈ graphLocalGroup (family P) v, Odd (orderOf x) ∧ x • w = z := by
  let := finite_endpoints h
  let J := graphLocalGroup (family P) v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hc : J.pCoreIn 2 = Q (family P) v := sylowGenerated_core _
  have hk : q.ker = (Q (family P) v).subgroupOf J := by
    rw [←hc]
    change q.ker = ((pCore 2 J).map J.subtype).comap J.subtype
    rw [comap_map_eq_self_of_injective J.subtype_injective]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  exact source_linear_odd_neighbor_transport h hB hS hvw hvz q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The original F1.11 local linear model gives transport in its reduced graph. -/
theorem reduced_linear_odd_neighbor_transport (h : HypothesisF11 L S) (j : Bool)
    (e : (family L j ⧸ pCore 2 (family L j)) ≃* PSL(2,F))
    {w z : Vertex (reducedFamily L S)}
    (hw : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) j) w)
    (hz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) j) z) :
    ∃ x ∈ graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) j),
      Odd (orderOf x) ∧ x • w = z := by
  let eSL : SL(2,F) ≃* PSL(2,F) := MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact source_linear_odd_neighbor_transport_of_quotient (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hw hz
    ((reduced_graphLinearQuotient h j e).trans eSL.symm)
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
