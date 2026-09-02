import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.IsSubnormal
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Theory.Comparator.Defs
import FeitThompson.PCore.PCore
import FeitThompson.PGroup.Omega

open scoped BigOperators Pointwise

universe u v

namespace Test
set_option autoImplicit false

def SL2 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
def L3 : Type := Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)
def S4 : Type := Equiv.Perm (Fin 4)
abbrev C4 : Type := Multiplicative (ZMod 4)
abbrev Q8 : Type := QuaternionGroup 2
instance : NeZero (2 : ℕ) := ⟨by decide⟩

def IsModel (H : Type u) [Group H] (X : Type v) [Group X] : Prop :=
  Nonempty (H ≃* X)

def IsCentralProductQ8Q8 (H : Type u) [Group H] [Finite H] : Prop :=
  ∃ A B : Subgroup H,
    IsModel A Q8 ∧ IsModel B Q8 ∧
    A ⊔ B = ⊤ ∧ Nat.card (A ⊓ B : Subgroup H) = 2 ∧
    (A ⊓ B) ≤ Subgroup.center H

def IsSemidirectC4Q8 (H : Type u) [Group H] [Finite H] : Prop :=
  ∃ φ : Q8 →* MulAut C4, IsModel H (SemidirectProduct C4 Q8 φ)

def NormalIn {G : Type u} [Group G] (K H : Subgroup G) : Prop :=
  K ≤ H ∧ (K.subgroupOf H).Normal

def SubnormalIn {G : Type u} [Group G] (K H : Subgroup G) : Prop :=
  K ≤ H ∧ (K.subgroupOf H).IsSubnormal

structure GraphData (G : Type u) [Group G] [Finite G] where
  Vertex : Type u
  [vertexFinite : Finite Vertex]
  [vertexAction : MulAction G Vertex]
  Gv : Vertex → Subgroup G
  Qv : Vertex → Subgroup G
  Ev : Vertex → Subgroup G
  Zv : Vertex → Subgroup G
  Vv : Vertex → Subgroup G
  qle : ∀ d : Vertex, Qv d ≤ Gv d
  qnormal : ∀ d : Vertex, ((Qv d).subgroupOf (Gv d)).Normal
  ele : ∀ d : Vertex, Ev d ≤ Gv d
  zle : ∀ d : Vertex, Zv d ≤ Gv d
  vle : ∀ d : Vertex, Vv d ≤ Gv d
  dist : Vertex → Vertex → ℕ
  Dv : Vertex → Set Vertex
  Dv_def : ∀ d l : Vertex, l ∈ Dv d ↔ dist l d = 1
  S : Subgroup G
  vtx0 : Vertex
  vtx1 : Vertex
  nextVertex : Vertex → Vertex
  prevVertex : Vertex → Vertex
  bval : ℕ

-- instances omitted

def qQuotient {G : Type u} [Group G] [Finite G] (C : GraphData G) (d : C.Vertex) : Type u :=
  letI := C.qnormal d
  C.Gv d ⧸ (C.Qv d).subgroupOf (C.Gv d)

noncomputable instance qQuotientGroup {G : Type u} [Group G] [Finite G]
    (C : GraphData G) (d : C.Vertex) : Group (qQuotient C d) := by
  dsimp [qQuotient]
  letI := C.qnormal d
  infer_instance

def QuotientModel {G : Type u} [Group G] [Finite G] (C : GraphData G)
    (d : C.Vertex) (X : Type*) [Group X] : Prop :=
  Nonempty (qQuotient C d ≃* X)

#check GraphData

end Test
