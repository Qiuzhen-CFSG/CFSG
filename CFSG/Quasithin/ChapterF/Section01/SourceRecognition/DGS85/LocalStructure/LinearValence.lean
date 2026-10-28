module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearMarking
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.SpecificGroups.SL2.BorelIndex
public import Theory.GroupTheory.AmalgamGraph.LinearPathKernel
/-!
# Valence and transported linear quotients

The intrinsic Sylow-generated local group supplements every incident edge
stabilizer. Hence it has the same neighbor index as the full vertex group.
An actual SL₂ quotient, with kernel the literal vertex two-core, identifies
the edge with a matrix Borel and computes this index as q+1. In particular
the forward branching is a power of two. Quotient markings at the two base
vertices transport by the original conjugation to every vertex.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 6.1--6.2 and the linear case of 6.7--6.8, pp.118--123. The actual
linear quotient is retained as an input; this does not prove 6.1.
-/

public noncomputable section
open Subgroup
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The intrinsic local group and the full vertex group have the same neighbor index. -/
theorem source_edge_index_local (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    (stabilizer (family P) w).relIndex (stabilizer (family P) v) =
      (stabilizer (family P) w).relIndex (graphLocalGroup (family P) v) := by
  let := finite_endpoints h
  let E := stabilizer (family P) v ⊓ stabilizer (family P) w
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer (family P) v from inf_le_left))
    (inclusion_injective _)
  have he := relIndex_sup_of_normalizes (graphLocalGroup (family P) v) E
    (inf_le_left.trans (sylowGenerated_normalized _))
  rw [graphLocalGroup_sup_edge h hB hS hvw] at he
  have hL : (stabilizer (family P) v).subgroupOf (graphLocalGroup (family P) v) = ⊤ :=
    subgroupOf_eq_top.mpr (sylowGenerated_le _)
  have hE : E.subgroupOf (graphLocalGroup (family P) v) =
      (stabilizer (family P) w).subgroupOf (graphLocalGroup (family P) v) := by
    change (stabilizer (family P) v).comap _ ⊓ (stabilizer (family P) w).comap _ = _
    rw [show (stabilizer (family P) v).comap (graphLocalGroup (family P) v).subtype = ⊤ from hL,top_inf_eq]
    rfl
  change E.relIndex (stabilizer (family P) v) = (E.subgroupOf (graphLocalGroup (family P) v)).index at he
  rw [hE] at he
  rw [show E = stabilizer (family P) v ⊓ stabilizer (family P) w from rfl,inf_relIndex_left] at he
  exact he

/-- An actual linear quotient computes the valence of its original vertex. -/
theorem source_linear_edge_index (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (q : graphLocalGroup (family P) v →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hq : Function.Surjective q)
    (hk : q.ker = (Q (family P) v).subgroupOf (graphLocalGroup (family P) v)) :
    (stabilizer (family P) w).relIndex (stabilizer (family P) v) = Nat.card K + 1 := by
  rw [source_edge_index_local h hB hS hvw]
  obtain ⟨a,ha⟩ := source_linear_borel_marking h hB hS hvw q hq hk
  change ((stabilizer (family P) w).subgroupOf (graphLocalGroup (family P) v)).index = _
  rw [ha,index_comap_of_surjective _ ((MulAut.conj a).surjective.comp hq)]
  exact Matrix.SpecialLinearGroup.rankOneBorel_index_even K

/-- The intrinsic local core quotient supplies the marked linear action. -/
theorem source_linear_edge_index_of_quotient (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) :
    (stabilizer (family P) w).relIndex (stabilizer (family P) v) = Nat.card K + 1 := by
  let := finite_endpoints h
  let L := graphLocalGroup (family P) v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hc : L.pCoreIn 2 = Q (family P) v := sylowGenerated_core _
  have hk : q.ker = (Q (family P) v).subgroupOf L := by
    rw [←hc]
    change q.ker = ((pCore 2 L).map L.subtype).comap L.subtype
    rw [comap_map_eq_self_of_injective L.subtype_injective]
    ext x
    change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  exact source_linear_edge_index h hB hS hvw q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk

/-- Linear quotients at the two base vertices discharge the actual binary branching premise. -/
theorem source_linear_branching (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (graphLocalGroup (family P) (base (family P) i) ⧸
      pCore 2 (graphLocalGroup (family P) (base (family P) i))) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (K i)) :
    ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k := by
  intro i
  let : Fintype (K i) := Fintype.ofFinite _
  obtain ⟨n,_,hn⟩ := FiniteField.card (K i) 2
  have hadj : (graph (family P)).Adj (base (family P) i) (base (family P) (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
  have he := source_linear_edge_index_of_quotient h hB hS hadj (e i)
  rw [show stabilizer (family P) (base (family P) i) = family P i from
      Subgroup.CosetGeometry.stabilizer_base _ _,
    show stabilizer (family P) (base (family P) (!i)) = family P (!i) from
      Subgroup.CosetGeometry.stabilizer_base _ _] at he
  refine ⟨n,?_⟩
  change (family P (!i)).relIndex (family P i) - 1 = _
  rw [he,Nat.add_sub_cancel,Nat.card_eq_fintype_card,hn]

/-- The given base quotient transports by the original conjugation to every vertex. -/
def source_linear_quotient_at (h : LocallyRankOneTriple P B)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (graphLocalGroup (family P) (base (family P) i) ⧸
      pCore 2 (graphLocalGroup (family P) (base (family P) i))) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (K i)) (v : Vertex (family P)) :
    (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (K v.type) := by
  let g := Classical.choose (Subgroup.CosetGeometry.exists_smul_base (family P) v)
  have hg := Classical.choose_spec (Subgroup.CosetGeometry.exists_smul_base (family P) v)
  let A := graphLocalGroup (family P) (base (family P) v.type)
  have heq : A.map (MulAut.conj g).toMonoidHom = graphLocalGroup (family P) v := by
    rw [←graphLocalGroup_conjugate h g,hg]
  let a : A ≃* graphLocalGroup (family P) v :=
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr heq)
  exact (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans (e v.type)
end CFSG.Quasithin.ChapterF.Source.DGS85
