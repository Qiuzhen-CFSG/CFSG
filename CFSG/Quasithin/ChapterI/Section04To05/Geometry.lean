module

public import CFSG.Quasithin.ChapterI.Section04To05.DSystem
public import Theory.GroupAction.TypedCosetGeometry
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# The coset geometry attached to a D-system

Points, lines and planes are the actual coset spaces of the three vertex
groups. Incidence is coset intersection; flags are pairwise incident sets.
Collinearity includes equality, whereas the point graph has no loops.

The kernel on the full geometry is the normal core of the common Sylow
subgroup, hence trivial by D4. The action on local chambers has kernel the
local two-core. Identifying local chambers with flags of the residues, and
proving faithfulness on points alone, require the further residue and
local-core arguments of I.5.3–8.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5,
printed pp. 419–422 (combined manuscript, 1 March 2004).
-/

@[expose] public section

namespace Quasithin.I5.DSystem

variable {G : Type*} [Group G] {D : Diagram} (S : DSystem D G)

abbrev Vertex := Subgroup.CosetGeometry.Vertex S.family
abbrev Point := G ⧸ S.family 0
abbrev Line := G ⧸ S.family 1
abbrev Plane := G ⧸ S.family 2
abbrev baseVertex := Subgroup.CosetGeometry.base S.family
abbrev Incident := Subgroup.CosetGeometry.Incident S.family
abbrev IsFlag := Subgroup.CosetGeometry.IsFlag S.family
abbrev Residue := Subgroup.CosetGeometry.Residue S.family

/-- Incidence between specified types. -/
def Inc {i j : Fin 3} (a : G ⧸ S.family i) (b : G ⧸ S.family j) : Prop :=
  S.Incident ⟨i, a⟩ ⟨j, b⟩

def basePoint : S.Point := (1 : G)
def baseLine : S.Line := (1 : G)
def basePlane : S.Plane := (1 : G)

/-- Points on a line, as an actual subset of the point coset space. -/
def pointsOn (l : S.Line) : Set S.Point := {x | S.Inc x l}

/-- Lines through a point. -/
def linesOn (x : S.Point) : Set S.Line := {l | S.Inc x l}

/-- Planes containing a point. -/
def planesOn (x : S.Point) : Set S.Plane := {p | S.Inc x p}

/-- Source collinearity: two points are incident with a common line. -/
def Collinear (x y : S.Point) : Prop := ∃ l : S.Line, S.Inc x l ∧ S.Inc y l

theorem collinear_symm {x y : S.Point} (h : S.Collinear x y) : S.Collinear y x := by
  obtain ⟨l, hx, hy⟩ := h
  exact ⟨l, hy, hx⟩

/-- Every point lies on a line, so source collinearity is reflexive. -/
theorem collinear_refl (x : S.Point) : S.Collinear x x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨(g : G ⧸ S.family 1), ⟨g, rfl, rfl⟩, ⟨g, rfl, rfl⟩⟩

/-- The collinearity graph Δ has distinct collinear points as adjacent vertices. -/
def pointGraph : SimpleGraph S.Point where
  Adj x y := x ≠ y ∧ S.Collinear x y
  symm := ⟨fun _ _ h => ⟨h.1.symm, S.collinear_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] theorem pointGraph_adj (x y : S.Point) :
    S.pointGraph.Adj x y ↔ x ≠ y ∧ S.Collinear x y := Iff.rfl

/-- The full incidence graph, with edges only between different types. -/
def incidenceGraph : SimpleGraph S.Vertex where
  Adj v w := v.type ≠ w.type ∧ S.Incident v w
  symm := ⟨fun _ _ h => ⟨h.1.symm, Subgroup.CosetGeometry.Incident.symm _ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The source bipartite graph Λ, on points and lines. -/
def pointLineGraph : SimpleGraph (S.Point ⊕ S.Line) where
  Adj a b := match a, b with
    | .inl x, .inr l => S.Inc x l
    | .inr l, .inl x => S.Inc x l
    | _, _ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> exact id⟩

@[simp] theorem pointLineGraph_adj (x : S.Point) (l : S.Line) :
    S.pointLineGraph.Adj (.inl x) (.inr l) ↔ S.Inc x l := Iff.rfl

/-- Source `R_x`: the subgroup of `Q₀` fixing every point collinear with `x`. -/
def neighborCore : Subgroup G :=
  S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Collinear S.basePoint y}

theorem neighborCore_le_Q : S.neighborCore ≤ S.Q 0 := inf_le_left

theorem neighborCore_fixes {g : G} (hg : g ∈ S.neighborCore) {y : S.Point}
    (hy : S.Collinear S.basePoint y) : g • y = y :=
  (mem_fixingSubgroup_iff G).mp hg.2 y hy

/-- The kernel on the entire coset geometry is the chamber normal core. -/
theorem geometry_kernel :
    (MulAction.toPermHom G S.Vertex).ker = S.T.normalCore :=
  Subgroup.CosetGeometry.action_kernel S.family

/-- I.5.4(4): the action on the full geometry is faithful. -/
theorem faithful_geometry : FaithfulSMul G S.Vertex :=
  Subgroup.CosetGeometry.faithful_of_core_free S.family S.core_free

@[simp] theorem stabilizer_basePoint : MulAction.stabilizer G S.basePoint = S.family 0 :=
  MulAction.stabilizer_quotient _

@[simp] theorem stabilizer_baseLine : MulAction.stabilizer G S.baseLine = S.family 1 :=
  MulAction.stabilizer_quotient _

@[simp] theorem stabilizer_basePlane : MulAction.stabilizer G S.basePlane = S.family 2 :=
  MulAction.stabilizer_quotient _

/-- The point-action kernel, before the additional proof that it is trivial. -/
theorem point_kernel : (MulAction.toPermHom G S.Point).ker = (S.family 0).normalCore :=
  (S.family 0).normalCore_eq_ker.symm

/-- The chambers at the standard vertex, presented as intrinsic local cosets. -/
abbrev LocalChamber (i : Fin 3) := S.family i ⧸ S.T.subgroupOf (S.family i)

/-- The local chamber action has exactly the intrinsic two-core as kernel. -/
theorem local_chamber_kernel (i : Fin 3) :
    (MulAction.toPermHom (S.family i) (S.LocalChamber i)).ker = pCore 2 (S.family i) :=
  (S.T.subgroupOf (S.family i)).normalCore_eq_ker.symm.trans (S.local_normalCore i)

/-- Translation preserves incidence. -/
theorem Inc.smul {i j : Fin 3} {a : G ⧸ S.family i} {b : G ⧸ S.family j}
    (h : S.Inc a b) (g : G) : S.Inc (g • a) (g • b) :=
  Subgroup.CosetGeometry.Incident.smul _ h g

/-- Translation preserves collinearity. -/
theorem Collinear.smul {x y : S.Point} (h : S.Collinear x y) (g : G) :
    S.Collinear (g • x) (g • y) := by
  obtain ⟨l, hx, hy⟩ := h
  exact ⟨g • l, hx.smul S g, hy.smul S g⟩

/-- Translation acts by automorphisms of the point graph. -/
theorem pointGraph_adj_smul_iff (g : G) (x y : S.Point) :
    S.pointGraph.Adj (g • x) (g • y) ↔ S.pointGraph.Adj x y := by
  constructor
  · intro ⟨hne, hcol⟩
    refine ⟨fun h => hne (congrArg (g • ·) h), ?_⟩
    simpa only [inv_smul_smul] using hcol.smul S g⁻¹
  · intro ⟨hne, hcol⟩
    exact ⟨fun h => hne ((MulAction.injective g) h), hcol.smul S g⟩

end Quasithin.I5.DSystem
