module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.LocalStructure
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The subgroup graph for J₂ recognition

Aschbacher, *Sporadic Groups* (1994), §47, pp.259–266, uses the conjugacy
class of order-three subgroups centralizing a conjugate of the distinguished
involution. Two vertices are adjacent when they generate A₄. `Seed` chooses
one such subgroup from the exact I.4.7 hypotheses; Cauchy's theorem supplies
it because the involution centralizer has order 1920.

Sylow conjugacy inside that centralizer proves that the graph includes the
conjugates of every order-three subgroup there, independently of the initial
choice. The action is literal left conjugation, its point stabilizers are
normalizers, and adjacency is preserved by subgroup isomorphisms. For simple
G the action is faithful: its kernel cannot be all of G, since that would make
the order-three seed normal in a group containing a subgroup of order 1920.

This module does not assert the later order 604800, the four suborbit sizes,
or uniqueness. Those require the remaining arguments of §47.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Janko23.J2Recognition

variable {G : Type*} [Group G] [Finite G]

/-- A local source witness with a chosen order-three subgroup of its centralizer. -/
structure Seed (G : Type*) [Group G] [Finite G] where
  z : G
  localType : HTypeAt z
  classes : TwoInvolutionClasses G
  X : Subgroup G
  card_X : Nat.card X = 3
  X_le : X ≤ involutionCentralizer z

/-- Every group of source type J₂ has an actual subgroup-graph seed. -/
theorem exists_seed (h : J2Type G) : Nonempty (Seed G) := by
  obtain ⟨⟨z, hz⟩, hc⟩ := h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := involutionCentralizer z) 3
    (by rw [hz.centralizer_card]; norm_num)
  refine ⟨⟨z, hz, hc, (zpowers x).map (involutionCentralizer z).subtype, ?_,
    map_subtype_le _⟩⟩
  rw [card_map_of_injective (involutionCentralizer z).subtype_injective,
    Nat.card_zpowers, hx]

namespace Seed
variable (D : Seed G)

/-- The ambient conjugacy class of the chosen subgroup. -/
abbrev Vertex := ↥(MulAction.orbit (ConjAct G) D.X)

instance : MulAction G D.Vertex :=
  MulAction.compHom _ ConjAct.toConjAct.toMonoidHom

/-- The distinguished vertex represented by the chosen subgroup itself. -/
def base : D.Vertex := ⟨D.X, MulAction.mem_orbit_self _⟩

theorem smul_val (g : G) (A : D.Vertex) :
    (g • A).val = A.val.map (MulAut.conj g).toMonoidHom := rfl

/-- The ambient group acts transitively on its subgroup conjugacy class. -/
theorem transitive (A : D.Vertex) : ∃ g : G, g • D.base = A := by
  obtain ⟨g, hg⟩ := A.property
  exact ⟨ConjAct.ofConjAct g, Subtype.ext hg⟩

theorem vertex_card (A : D.Vertex) : Nat.card A.val = 3 := by
  obtain ⟨g, hg⟩ := D.transitive A
  rw [← hg, D.smul_val, card_map_of_injective (MulAut.conj g).injective]
  exact D.card_X

/-- All order-three subgroups of the source centralizer are conjugate inside it. -/
theorem conjugate_of_le_centralizer (Y : Subgroup G) (hY : Nat.card Y = 3)
    (hYH : Y ≤ involutionCentralizer D.z) :
    ∃ g : involutionCentralizer D.z, ConjAct.toConjAct (g : G) • D.X = Y := by
  let H := involutionCentralizer D.z
  have hc (A : Subgroup G) (hA : Nat.card A = 3) (hAH : A ≤ H) :
      Nat.card (A.subgroupOf H) = 3 ^ (Nat.card H).factorization 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv, hA,
      D.localType.centralizer_card]
    decide +kernel
  let P : Sylow 3 H := Sylow.ofCard (D.X.subgroupOf H) (hc D.X D.card_X D.X_le)
  let Q : Sylow 3 H := Sylow.ofCard (Y.subgroupOf H) (hc Y hY hYH)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P Q
  have he := congrArg (fun S : Sylow 3 H => (S : Subgroup H)) hg
  change MulAut.conj g • D.X.subgroupOf H = Y.subgroupOf H at he
  rw [conj_smul_subgroupOf D.X_le g] at he
  have hm := congrArg (fun S : Subgroup H => S.map H.subtype) he
  rw [map_subgroupOf_eq_of_le (conj_smul_le_of_le D.X_le g),
    map_subgroupOf_eq_of_le hYH] at hm
  exact ⟨g, hm⟩

theorem mem_vertex_of_le_centralizer (Y : Subgroup G) (hY : Nat.card Y = 3)
    (hYH : Y ≤ involutionCentralizer D.z) : Y ∈ MulAction.orbit (ConjAct G) D.X := by
  obtain ⟨g, hg⟩ := D.conjugate_of_le_centralizer Y hY hYH
  exact ⟨ConjAct.toConjAct (g : G), hg⟩

/-- The chosen orbit is exactly the union of the conjugacy classes used in §47. -/
theorem mem_vertex_iff (A : Subgroup G) :
    A ∈ MulAction.orbit (ConjAct G) D.X ↔
      ∃ Y : Subgroup G, Nat.card Y = 3 ∧ Y ≤ involutionCentralizer D.z ∧
        ∃ g : G, ConjAct.toConjAct g • Y = A := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨D.X, D.card_X, D.X_le, ConjAct.ofConjAct g, hg⟩
  · rintro ⟨Y, hY, hYH, g, rfl⟩
    exact MulAction.mem_orbit_of_mem_orbit _ (D.mem_vertex_of_le_centralizer Y hY hYH)

/-- Every vertex centralizes a conjugate of the specified source involution. -/
theorem vertex_centralizes_conjugate (A : D.Vertex) :
    ∃ t : G, IsConj D.z t ∧ A.val ≤ involutionCentralizer t := by
  obtain ⟨g, rfl⟩ := D.transitive A
  refine ⟨g * D.z * g⁻¹, isConj_iff.mpr ⟨g, rfl⟩, ?_⟩
  rw [D.smul_val]
  rintro _ ⟨x, hx, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  change (MulAut.conj g) x * (MulAut.conj g) D.z =
    (MulAut.conj g) D.z * (MulAut.conj g) x
  have hc := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp (D.X_le hx))
  simpa only [map_mul] using hc

/-- The vertex stabilizer is the literal ambient subgroup normalizer. -/
theorem stabilizer_eq_normalizer (A : D.Vertex) :
    MulAction.stabilizer G A = normalizer (A.val : Set G) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
  exact Subgroup.conjAct_pointwise_smul_iff

/-- The graph of §47: adjacent order-three subgroups generate A₄. -/
def graph : SimpleGraph D.Vertex where
  Adj A B := A ≠ B ∧ Nonempty (↥(A.val ⊔ B.val) ≃* alternatingGroup (Fin 4))
  symm := ⟨by
    intro A B h
    refine ⟨h.1.symm, ?_⟩
    rw [sup_comm B.val A.val]
    exact h.2⟩
  loopless := ⟨fun A h => h.1 rfl⟩

/-- For these vertices, the A₄ condition itself already excludes loops. -/
theorem graph_adj_iff (A B : D.Vertex) :
    D.graph.Adj A B ↔ Nonempty (↥(A.val ⊔ B.val) ≃* alternatingGroup (Fin 4)) := by
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  intro he
  subst B
  obtain ⟨e⟩ := h
  have hc := Nat.card_congr e.toEquiv
  rw [sup_idem, D.vertex_card, nat_card_alternatingGroup] at hc
  norm_num at hc

theorem preserves (g : G) {A B : D.Vertex} (h : D.graph.Adj A B) :
    D.graph.Adj (g • A) (g • B) := by
  apply (D.graph_adj_iff _ _).mpr
  obtain ⟨e⟩ := h.2
  have hm : (A.val ⊔ B.val).map (MulAut.conj g).toMonoidHom =
      (g • A).val ⊔ (g • B).val := by rw [Subgroup.map_sup, D.smul_val, D.smul_val]
  exact ⟨(MulEquiv.subgroupCongr hm.symm).trans
    (((A.val ⊔ B.val).equivMapOfInjective _ (MulAut.conj g).injective).symm.trans e)⟩

theorem X_ne_bot : D.X ≠ ⊥ := by
  intro he
  have hc := D.card_X
  rw [he, card_bot] at hc
  omega

theorem X_ne_top : D.X ≠ ⊤ := by
  intro he
  have hc := D.card_X
  rw [he, card_top] at hc
  have hb := Nat.card_le_card_of_injective _ (involutionCentralizer D.z).subtype_injective
  rw [D.localType.centralizer_card, hc] at hb
  omega

theorem X_not_normal [IsSimpleGroup G] : ¬ D.X.Normal := by
  intro hn
  exact hn.eq_bot_or_eq_top.elim D.X_ne_bot D.X_ne_top

/-- Simplicity makes this nontrivial conjugation action faithful. -/
theorem faithful [IsSimpleGroup G] (g : G) (hg : ∀ A : D.Vertex, g • A = A) : g = 1 := by
  let f := MulAction.toPermHom G D.Vertex
  have hf : f.ker = ⊥ := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      apply D.X_not_normal
      apply Subgroup.Normal.of_conjugate_fixed
      intro a
      have ha : f a = 1 := MonoidHom.mem_ker.mp (h ▸ mem_top a)
      exact congrArg (fun p : Equiv.Perm D.Vertex => (p D.base).val) ha
  apply (f.ker_eq_bot_iff.mp hf)
  rw [map_one]
  exact Equiv.ext hg

end Seed
end CFSG.Quasithin.Janko23.J2Recognition
