module

public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.AlgebraicGroup.BNPair.DihedralGeometry
public import Theory.GroupAction.SylowCosetFixedPoints
public import Theory.GroupAction.EvenPolygonFixedPoints
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-!
# The genuine triality parabolic coset action

Vertices are typed left cosets of the two full root parabolics of the pinned
D4 graph-field carrier. The standard apartment is the orbit of their standard
vertices under the actual BN-pair normalizer. The proved Sylow calculation puts
every two-subgroup in a chamber stabilizer, including at q = 2.

The hexagon metric and conjugacy of its twelve-cycles, and oddness of the
standard apartment fixer, are separate geometric obligations. The definitions
below contain neither normalizer coverage nor quasithinness. Once these inputs
are supplied, the finite-tree argument gives coverage of arbitrary nonidentity
two-subgroup normalizers, without characteristic-subgroup restrictions.

Sources: GLS3 §§2.3, 2.6 and Theorem 3.1.3
(`refs/KGroup/GLS3/chapter2.tex`, `chapter3.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.TwoLocalGeometry

open Subgroup Parabolics GroupAction.EvenPolygon
open Theory.AlgebraicGroup.TitsSystem
open scoped Pointwise

/-- The actual full-parabolic left cosets; the local residuals are not used
as vertex stabilizers. -/
abbrev Vertex (f : ℕ) (hf : 0 < f) :=
  CosetGeometry.Vertex (parabolic (binaryParameters f hf))

instance (f : ℕ) (hf : 0 < f) : Finite (Vertex f hf) := by
  let F := parabolic (binaryParameters f hf)
  let toSum : Vertex f hf → (Carrier (binaryParameters f hf) ⧸ F .arms) ⊕
      (Carrier (binaryParameters f hf) ⧸ F .central) := fun v =>
    match v with
    | ⟨.arms, q⟩ => Sum.inl q
    | ⟨.central, q⟩ => Sum.inr q
  apply Finite.of_injective toSum
  rintro ⟨a, q⟩ ⟨b, r⟩ h
  cases a <;> cases b <;> simp_all [toSum]

def vertexColor {f : ℕ} {hf : 0 < f} (v : Vertex f hf) : Bool :=
  match v.type with
  | .arms => false
  | .central => true

/-- Incidence joins distinct types whose left cosets intersect. -/
abbrev incidenceGraph (f : ℕ) (hf : 0 < f) : SimpleGraph (Vertex f hf) :=
  DihedralGeometry.graph (parabolic (binaryParameters f hf))

theorem adjacent_color {f : ℕ} {hf : 0 < f} {v w : Vertex f hf}
    (h : (incidenceGraph f hf).Adj v w) : vertexColor v ≠ vertexColor w := by
  obtain ⟨a, v⟩ := v
  obtain ⟨b, w⟩ := w
  cases a <;> cases b <;> simp_all [incidenceGraph, DihedralGeometry.graph, vertexColor]

theorem smul_adj {f : ℕ} {hf : 0 < f} (g : Carrier (binaryParameters f hf))
    {v w : Vertex f hf} (h : (incidenceGraph f hf).Adj v w) :
    (incidenceGraph f hf).Adj (g • v) (g • w) :=
  ⟨h.1, h.2.smul _ g⟩

@[simp] theorem smul_color {f : ℕ} {hf : 0 < f}
    (g : Carrier (binaryParameters f hf)) (v : Vertex f hf) :
    vertexColor (g • v) = vertexColor v := rfl

/-- The concrete hexagon assertions. No local normalizer conclusion is a field. -/
structure HexagonGeometry (f : ℕ) (hf : 0 < f) : Prop where
  diameter_bound : ∀ v w : Vertex f hf,
    ∃ p : (incidenceGraph f hf).Walk v w, p.length ≤ 6
  cycle_bound : ∀ v (p : (incidenceGraph f hf).Walk v v), p.IsCycle → 12 ≤ p.length

/-- The normalizer orbit of the two standard vertices, in the genuine action. -/
def standardApartment (f : ℕ) (hf : 0 < f) : Set (Vertex f hf) :=
  DihedralGeometry.apartment (ConcreteBruhat.titsSystem f hf)
    (parabolic (binaryParameters f hf))

/-- Twelve-cycles are translates of the actual standard apartment. -/
def ApartmentTranslates (f : ℕ) (hf : 0 < f) : Prop :=
  ∀ v (p : (incidenceGraph f hf).Walk v v), p.IsCycle → p.length = 12 →
    ∃ g : Carrier (binaryParameters f hf),
      g • standardApartment f hf = {w | w ∈ p.support}

theorem base_mem_standardApartment (f : ℕ) (hf : 0 < f) (a : Node) :
    CosetGeometry.base (parabolic (binaryParameters f hf)) a ∈ standardApartment f hf :=
  DihedralGeometry.base_mem_apartment _ _ a

/-- The actual apartment fixer lies in the Borel, because it fixes both
standard vertices. -/
theorem standardApartment_fixer_le_borel (f : ℕ) (hf : 0 < f) :
    fixingSubgroup (Carrier (binaryParameters f hf)) (standardApartment f hf) ≤
      borel (binaryParameters f hf) := by
  rw [← parabolic_inf_binary (binaryParameters f hf) rfl]
  apply le_inf
  all_goals
    intro x hx
    rw [← CosetGeometry.stabilizer_base (parabolic (binaryParameters f hf))]
    exact (mem_fixingSubgroup_iff _).mp hx _ (base_mem_standardApartment f hf _)

/-- Containment in the actual torus suffices to prove fixer oddness; its exact
order and the full triality group order are unnecessary. -/
theorem standardApartment_fixer_odd_of_le_torus (f : ℕ) (hf : 0 < f)
    (hle : fixingSubgroup (Carrier (binaryParameters f hf)) (standardApartment f hf) ≤
      ConcreteBruhat.torus (binaryParameters f hf)) :
    Odd (Nat.card (fixingSubgroup (Carrier (binaryParameters f hf))
      (standardApartment f hf))) := by
  have htorus : Odd (Nat.card (ConcreteBruhat.torus (binaryParameters f hf))) := by
    rw [ConcreteBruhat.TorusCoordinates.card_torus _ rfl]
    exact ConcreteBruhat.TorusCoordinates.odd_torus_order _ rfl
  exact htorus.of_dvd_nat (card_dvd_of_le hle)

/-- Translation conjugates the pointwise fixers, preserving their orders. -/
theorem odd_apartment_stabilizers {f : ℕ} {hf : 0 < f}
    (htrans : ApartmentTranslates f hf)
    (hodd : Odd (Nat.card (fixingSubgroup (Carrier (binaryParameters f hf))
      (standardApartment f hf))))
    (v : Vertex f hf) (p : (incidenceGraph f hf).Walk v v)
    (hp : p.IsCycle) (hlen : p.length = 12) :
    Odd (Nat.card (fixingSubgroup (Carrier (binaryParameters f hf))
      {w | w ∈ p.support})) := by
  obtain ⟨g, hg⟩ := htrans v p hp hlen
  rw [← Nat.card_congr (SubMulAction.fixingSubgroupEquivFixingSubgroup hg).toEquiv]
  exact hodd

/-- Combine metric geometry and apartment-fixer oddness with the proved
action laws. The concrete geometric premises remain explicit. -/
theorem HexagonGeometry.toEvenPolygonAction {f : ℕ} {hf : 0 < f}
    (h : HexagonGeometry f hf) (htrans : ApartmentTranslates f hf)
    (hodd : Odd (Nat.card (fixingSubgroup (Carrier (binaryParameters f hf))
      (standardApartment f hf)))) :
    EvenPolygonAction (G := Carrier (binaryParameters f hf)) 3
      (incidenceGraph f hf) vertexColor where
  adjacent_color := adjacent_color
  smul_adj := smul_adj
  smul_color := smul_color
  diameter_bound := h.diameter_bound
  cycle_bound := h.cycle_bound
  apartment_stabilizer_odd := odd_apartment_stabilizers htrans hodd

/-- Every two-subgroup fixes an incident pair. This uses the proved concrete
Sylow theorem and has no outstanding index or conjugacy premise. -/
theorem exists_fixed_edge (f : ℕ) (hf : 0 < f)
    (R : Subgroup (Carrier (binaryParameters f hf))) (hR : IsPGroup 2 R) :
    ∃ v w : Vertex f hf, (incidenceGraph f hf).Adj v w ∧
      v ∈ fixedVertices R ∧ w ∈ fixedVertices R := by
  let P := binaryParameters f hf
  obtain ⟨g, hg⟩ := CosetGeometry.exists_fixed_chamber (parabolic P)
    (unipotentSylow P rfl)
    (fun a => (unipotent_le_borel P).trans (borel_le_parabolic P a)) R hR
  exact ⟨g • CosetGeometry.base (parabolic P) .arms,
    g • CosetGeometry.base (parabolic P) .central,
    smul_adj g ⟨by change Node.arms ≠ Node.central; decide,
      CosetGeometry.incident_base _ _ _⟩, hg _, hg _⟩

end Triality.Standard.TwoLocalGeometry
