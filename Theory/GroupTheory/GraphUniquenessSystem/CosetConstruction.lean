module

public import Theory.GroupTheory.GraphUniquenessSystem
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Order.Atoms

/-!
# Uniqueness systems on actual left cosets

For subgroups M and H and an element t of H outside M, vertices are G/M
and edges are translates of {M,tM}. We compute the stabilizers using left
conjugation, prove transitivity, and obtain faithfulness from the normal
core of M. Relative maximality of H ∩ M in H and M proves the two local
generation identities once the edge fixer contains an element outside H.
Only global generation remains an explicit generation premise.

Coset incidence retains a second subgroup P. Transitivity of its point
stabilizer on the other points of the base line identifies the orbit graph
with the collinearity graph of G/M and G/P.

The constructor is conditional. It does not assert existence of M, H or t,
or prove that any particular finite group satisfies these local hypotheses.
Its source application is Aschbacher–Segev, *The study of J₄ via the theory
of uniqueness systems*, (3.1), (3.2), (5.1), pp.16–20.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] (M : Subgroup G)

abbrev Vertex := G ⧸ M

def vertex (g : G) : Vertex M := QuotientGroup.mk g

@[simp] theorem smul_vertex (g a : G) : g • vertex M a = vertex M (g * a) := rfl

theorem vertex_eq_iff (g a : G) : vertex M g = vertex M a ↔ g⁻¹ * a ∈ M :=
  QuotientGroup.eq

@[simp] theorem vertex_eq_base (g : G) : vertex M g = vertex M 1 ↔ g ∈ M := by
  rw [vertex_eq_iff]
  simp

@[simp] theorem stabilizer_vertex (g : G) :
    MulAction.stabilizer G (vertex M g) = M.comap (MulAut.conj g⁻¹).toMonoidHom := by
  ext a
  change vertex M (a * g) = vertex M g ↔ g⁻¹ * a * (g⁻¹)⁻¹ ∈ M
  rw [eq_comm, vertex_eq_iff]
  simp only [inv_inv, mul_assoc]

@[simp] theorem stabilizer_base : MulAction.stabilizer G (vertex M 1) = M :=
  MulAction.stabilizer_quotient M

theorem transitive (a : Vertex M) : ∃ g : G, g • vertex M 1 = a := by
  induction a using QuotientGroup.induction_on with
  | H g => exact ⟨g, by simp [vertex]⟩

theorem faithful (hM : M.normalCore = ⊥) (g : G)
    (hg : ∀ a : Vertex M, g • a = a) : g = 1 := by
  have hm : g ∈ (MulAction.toPermHom G (Vertex M)).ker := Equiv.ext hg
  rw [← M.normalCore_eq_ker, hM] at hm
  exact hm

variable (t : G)

def Adj (a b : Vertex M) : Prop :=
  ∃ g : G, (vertex M g = a ∧ vertex M (g * t) = b) ∨
    (vertex M g = b ∧ vertex M (g * t) = a)

def graph (ht : t ∉ M) : SimpleGraph (Vertex M) where
  Adj := Adj M t
  symm := ⟨by
    rintro a b ⟨g, hab | hab⟩
    · exact ⟨g, Or.inr hab⟩
    · exact ⟨g, Or.inl hab⟩⟩
  loopless := ⟨by
    rintro a ⟨g, he | he⟩ <;>
      have hm := (vertex_eq_iff M g (g * t)).mp (he.1.trans he.2.symm) <;>
      exact ht (by simpa using hm)⟩

theorem graph_adj_base (ht : t ∉ M) : (graph M t ht).Adj (vertex M 1) (vertex M t) :=
  ⟨1, Or.inl ⟨rfl, by simp⟩⟩

theorem preserves (ht : t ∉ M) (g : G) {a b : Vertex M}
    (hab : (graph M t ht).Adj a b) : (graph M t ht).Adj (g • a) (g • b) := by
  obtain ⟨k, he | he⟩ := hab
  · rcases he with ⟨rfl, rfl⟩
    exact ⟨g * k, Or.inl ⟨rfl, by simp only [smul_vertex, mul_assoc]⟩⟩
  · rcases he with ⟨rfl, rfl⟩
    exact ⟨g * k, Or.inr ⟨rfl, by simp only [smul_vertex, mul_assoc]⟩⟩

theorem edge_transitive (ht : t ∉ M) (a b : Vertex M)
    (hab : (graph M t ht).Adj a b) :
    ∃ g : G, (g • vertex M 1 = a ∧ g • vertex M t = b) ∨
      (g • vertex M 1 = b ∧ g • vertex M t = a) := by
  change Adj M t a b at hab
  simpa only [Adj, smul_vertex, mul_one] using hab

theorem edgeFixer_eq :
    GraphUniquenessSystem.edgeFixer G (vertex M 1) (vertex M t) =
      M ⊓ M.comap (MulAut.conj t⁻¹).toMonoidHom := by
  rw [GraphUniquenessSystem.edgeFixer, stabilizer_base, stabilizer_vertex]

theorem swap (ht2 : t * t ∈ M) :
    t • vertex M 1 = vertex M t ∧ t • vertex M t = vertex M 1 := by
  exact ⟨by simp, (vertex_eq_base M _).mpr ht2⟩

/-- Incidence in the actual coset geometry means a common representative. -/
def Incident (P : Subgroup G) (a : Vertex M) (l : Vertex P) : Prop :=
  ∃ g : G, vertex M g = a ∧ vertex P g = l

/-- Distinct points are collinear when they share an actual coset of P. -/
def Collinear (P : Subgroup G) (a b : Vertex M) : Prop :=
  a ≠ b ∧ ∃ l : Vertex P, Incident M P a l ∧ Incident M P b l

/-- The line stabilizer fixes the base point and is transitive on the other
points of its line. This is the precise local action used below. -/
def LineTransitive (P : Subgroup G) : Prop :=
  ∀ u : G, u ∈ P → u ∉ M → ∃ p : G, p ∈ P ∧
    vertex M p = vertex M 1 ∧ vertex M (p * t) = vertex M u

theorem adj_iff_collinear (P : Subgroup G) (ht : t ∉ M) (htP : t ∈ P)
    (hP : LineTransitive M t P) (a b : Vertex M) :
    (graph M t ht).Adj a b ↔ Collinear M P a b := by
  constructor
  · intro hab
    refine ⟨hab.ne, ?_⟩
    obtain ⟨g, he | he⟩ := hab
    · rcases he with ⟨rfl, rfl⟩
      refine ⟨vertex P g, ⟨g, rfl, rfl⟩, g * t, rfl, ?_⟩
      apply Eq.symm
      apply (vertex_eq_iff P _ _).mpr
      simpa using htP
    · rcases he with ⟨rfl, rfl⟩
      refine ⟨vertex P g, ⟨g * t, rfl, ?_⟩, g, rfl, rfl⟩
      apply Eq.symm
      apply (vertex_eq_iff P _ _).mpr
      simpa using htP
  · rintro ⟨hne, l, ⟨g, rfl, hg⟩, k, rfl, hk⟩
    have huP : g⁻¹ * k ∈ P := (vertex_eq_iff P _ _).mp (hg.trans hk.symm)
    have huM : g⁻¹ * k ∉ M := fun hm => hne ((vertex_eq_iff M _ _).mpr hm)
    obtain ⟨p, _, hp, hpt⟩ := hP (g⁻¹ * k) huP huM
    refine ⟨g * p, Or.inl ⟨?_, ?_⟩⟩
    · simpa only [smul_vertex, mul_one] using congrArg (fun a => g • a) hp
    · simpa only [smul_vertex, mul_assoc, mul_inv_cancel_left] using
        congrArg (fun a => g • a) hpt

private theorem sup_inter_eq_of_maximal (H M B : Subgroup G)
    (hmax : IsCoatom (H.subgroupOf M)) (hB : B ≤ M) (hnot : ¬ B ≤ H) :
    B ⊔ (H ⊓ M) = M := by
  have hle : B ⊔ (H ⊓ M) ≤ M := sup_le hB inf_le_right
  have hi : H.subgroupOf M ≤ (B ⊔ (H ⊓ M)).subgroupOf M :=
    fun a ha => mem_sup_right ⟨ha, a.property⟩
  have htop : (B ⊔ (H ⊓ M)).subgroupOf M = ⊤ := by
    apply (hmax.ne_iff_eq_top hi).mp
    intro he
    apply hnot
    intro b hb
    have hm : (⟨b, hB hb⟩ : M) ∈ (B ⊔ (H ⊓ M)).subgroupOf M := mem_sup_left hb
    rw [he] at hm
    exact hm
  apply le_antisymm hle
  intro a ha
  have hm : (⟨a, ha⟩ : M) ∈ (B ⊔ (H ⊓ M)).subgroupOf M := by rw [htop]; trivial
  exact hm

open GraphUniquenessSystem

variable (H : Subgroup G)

def system (htH : t ∈ H) (htM : t ∉ M) (ht2 : t * t ∈ M)
    (hfaithful : M.normalCore = ⊥) (hgenerate : H ⊔ M = ⊤)
    (hvertex : IsCoatom (H.subgroupOf M)) (hlocal : IsCoatom (M.subgroupOf H))
    (hedge : ¬ M ⊓ M.comap (MulAut.conj t⁻¹).toMonoidHom ≤ H) :
    System G (Vertex M) where
  graph := graph M t htM
  H := H
  x := vertex M 1
  y := vertex M t
  adjacent := graph_adj_base M t htM
  preserves := preserves M t htM
  faithful := faithful M hfaithful
  vertex_transitive := transitive M
  edge_transitive := edge_transitive M t htM
  local_orbit := ⟨⟨t, htH⟩, by simp⟩
  generate := by rwa [stabilizer_base]
  vertex_generate := by
    rw [stabilizer_base, edgeFixer_eq]
    exact sup_inter_eq_of_maximal H M _ hvertex inf_le_left hedge
  local_generate := by
    rw [stabilizer_base, inf_comm H M]
    apply sup_inter_eq_of_maximal M H _ hlocal inf_le_left
    intro hle
    exact htM (hle ⟨htH, Or.inr (swap M t ht2)⟩)

@[simp] theorem system_local (htH : t ∈ H) (htM : t ∉ M) (ht2 : t * t ∈ M)
    (hfaithful : M.normalCore = ⊥) (hgenerate : H ⊔ M = ⊤)
    (hvertex : IsCoatom (H.subgroupOf M)) (hlocal : IsCoatom (M.subgroupOf H))
    (hedge : ¬ M ⊓ M.comap (MulAut.conj t⁻¹).toMonoidHom ≤ H) :
    (system M t H htH htM ht2 hfaithful hgenerate hvertex hlocal hedge).H = H := rfl

@[simp] theorem system_vertexGroup (htH : t ∈ H) (htM : t ∉ M) (ht2 : t * t ∈ M)
    (hfaithful : M.normalCore = ⊥) (hgenerate : H ⊔ M = ⊤)
    (hvertex : IsCoatom (H.subgroupOf M)) (hlocal : IsCoatom (M.subgroupOf H))
    (hedge : ¬ M ⊓ M.comap (MulAut.conj t⁻¹).toMonoidHom ≤ H) :
    (system M t H htH htM ht2 hfaithful hgenerate hvertex hlocal hedge).vertexGroup = M :=
  stabilizer_base M

end Theory.GroupTheory.GraphUniquenessSystem.Cosets
