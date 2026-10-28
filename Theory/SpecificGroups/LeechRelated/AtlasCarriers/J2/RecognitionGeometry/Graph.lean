module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.Edge
public import Theory.GroupTheory.GraphUniquenessSystem

/-!
# The concrete Hall–Janko subgroup graph

Vertices are the conjugates of the fixed cyclic subgroup X inside the ATLAS
carrier. Adjacency is isomorphism of the literal subgroup join with A₄.
The short conjugator supplies an actual adjacent vertex. Stabilizers are
literal normalizers, so later local computations apply without a transport
of the carrier or a choice of an abstract graph.

Source: Aschbacher, *Sporadic Groups* (1994), 47.5 and 47.10, pp.263–267.
Faithfulness, neighbor transitivity and the three generation identities are
separate concrete local calculations, not conclusions of this module.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry
open Subgroup Theory.GroupTheory.GraphUniquenessSystem
open scoped Pointwise

abbrev Vertex := ↥(MulAction.orbit (ConjAct Carrier) X)

instance : MulAction Carrier Vertex :=
  MulAction.compHom _ ConjAct.toConjAct.toMonoidHom

def base : Vertex := ⟨X, MulAction.mem_orbit_self _⟩

def neighbor : Vertex := ⟨Y, ⟨ConjAct.toConjAct conjugator, Y_eq_map.symm⟩⟩

theorem smul_val (g : Carrier) (A : Vertex) :
    (g • A).val = A.val.map (MulAut.conj g).toMonoidHom := rfl

theorem transitive (A : Vertex) : ∃ g : Carrier, g • base = A := by
  obtain ⟨g, hg⟩ := A.property
  exact ⟨ConjAct.ofConjAct g, Subtype.ext hg⟩

theorem vertex_card (A : Vertex) : Nat.card A.val = 3 := by
  obtain ⟨g, hg⟩ := transitive A
  rw [← hg, smul_val]
  exact (card_map_of_injective (K := X) (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective).trans card_X

theorem stabilizer_eq_normalizer (A : Vertex) :
    MulAction.stabilizer Carrier A = normalizer (A.val : Set Carrier) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
  exact Subgroup.conjAct_pointwise_smul_iff

def graph : SimpleGraph Vertex where
  Adj A B := A ≠ B ∧ Nonempty (↥(A.val ⊔ B.val) ≃* alternatingGroup (Fin 4))
  symm := ⟨by
    intro A B h
    refine ⟨h.1.symm, ?_⟩
    rw [sup_comm B.val A.val]
    exact h.2⟩
  loopless := ⟨fun A h => h.1 rfl⟩

theorem graph_adj_iff (A B : Vertex) :
    graph.Adj A B ↔ Nonempty (↥(A.val ⊔ B.val) ≃* alternatingGroup (Fin 4)) := by
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  intro he
  subst B
  obtain ⟨e⟩ := h
  have hc := Nat.card_congr e.toEquiv
  rw [sup_idem, vertex_card, nat_card_alternatingGroup] at hc
  norm_num [Nat.factorial] at hc

theorem preserves (g : Carrier) {A B : Vertex} (h : graph.Adj A B) :
    graph.Adj (g • A) (g • B) := by
  apply (graph_adj_iff _ _).mpr
  obtain ⟨e⟩ := h.2
  have hm : (A.val ⊔ B.val).map (MulAut.conj g).toMonoidHom =
      (g • A).val ⊔ (g • B).val := by rw [Subgroup.map_sup, smul_val, smul_val]
  exact ⟨(MulEquiv.subgroupCongr hm.symm).trans
    (((A.val ⊔ B.val).equivMapOfInjective _ (MulAut.conj g).injective).symm.trans e)⟩

theorem adjacent : graph.Adj base neighbor :=
  (graph_adj_iff _ _).mpr ⟨edgeEquiv⟩

theorem base_stabilizer : MulAction.stabilizer Carrier base = M :=
  stabilizer_eq_normalizer base

theorem edgeFixer_eq : edgeFixer Carrier base neighbor = E := by
  rw [edgeFixer, base_stabilizer, stabilizer_eq_normalizer]
  rfl

theorem t_smul_base : t • base = neighbor := by
  apply Subtype.ext
  change X.map (MulAut.conj t).toMonoidHom = Y
  rw [X, MonoidHom.map_zpowers]
  exact congrArg zpowers t_conj_x

theorem t_smul_neighbor : t • neighbor = base := by
  apply Subtype.ext
  change Y.map (MulAut.conj t).toMonoidHom = X
  rw [Y, MonoidHom.map_zpowers]
  exact congrArg zpowers t_conj_y

end Sporadic.LeechRelated.J2.RecognitionGeometry
