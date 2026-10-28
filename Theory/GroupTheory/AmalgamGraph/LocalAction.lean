module
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.GroupTheory.AmalgamLocalCores

/-!
# Local actions in general rank-two coset graphs

The stabilizer acts on the literal neighbor set. Its permutation kernel is
exactly the pointwise fixer of the closed radius-one ball and the relative
normal core of any incident edge group. Finite endpoint groups make every
neighbor set finite, even for an infinite completion. An edge containing a
vertex Sylow identifies the kernel's embedded two-core with the vertex core;
it does not identify the entire kernel with its core.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 3.1--3.3 and Hypothesis A', pp.71--75 and 94--95.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry (exists_smul_base translationGraphIso incident_base)
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- The literal permutation action of a vertex stabilizer on its neighbors. -/
def localAction (v : Vertex F) : stabilizer F v →* Equiv.Perm ((graph F).neighborSet v) where
  toFun g :=
    { toFun w := ⟨(g : G) • w.val, by
        have h := (translationGraphIso F (g : G)).map_adj_iff.mpr w.property
        change (graph F).Adj ((g : G) • v) ((g : G) • w.val) at h
        rwa [g.property] at h⟩
      invFun w := ⟨(g : G)⁻¹ • w.val, by
        have h := (translationGraphIso F (g : G)⁻¹).map_adj_iff.mpr w.property
        have hg : (g : G)⁻¹ • v = v := (stabilizer F v).inv_mem g.property
        change (graph F).Adj ((g : G)⁻¹ • v) ((g : G)⁻¹ • w.val) at h
        rwa [hg] at h⟩
      left_inv w := Subtype.ext (inv_smul_smul (g : G) w.val)
      right_inv w := Subtype.ext (smul_inv_smul (g : G) w.val) }
  map_one' := by ext w; exact one_smul G w.val
  map_mul' g h := by ext w; exact mul_smul (g : G) (h : G) w.val

@[simp] theorem localAction_apply (v : Vertex F) (g : stabilizer F v)
    (w : (graph F).neighborSet v) : (localAction F v g w).val = (g : G) • w.val := rfl

/-- This action kernel fixes the closed radius-one neighborhood, not just its center. -/
theorem localAction_ker (v : Vertex F) :
    (localAction F v).ker = (ballKernel F v 1).subgroupOf (stabilizer F v) := by
  ext g
  constructor
  · intro hg w hw
    rcases (mem_ball_one F v w).mp hw with hw | rfl
    · exact congrArg Subtype.val (Equiv.Perm.ext_iff.mp hg ⟨w, hw⟩)
    · exact g.property
  · intro hg
    apply Equiv.Perm.ext
    intro w
    exact Subtype.ext (hg w.val ((mem_ball_one F v w.val).mpr (Or.inl w.property)))

/-- The source local permutation kernel is the normal core of the whole edge group. -/
theorem localAction_ker_eq_edge_core {v w : Vertex F} (h : (graph F).Adj v w) :
    (localAction F v).ker =
      ((stabilizer F v ⊓ stabilizer F w).subgroupOf (stabilizer F v)).normalCore := by
  rw [localAction_ker, ballKernel_one_eq_normalCore F h]

/-- Finite vertex groups imply locally finite coset graphs, with no finite completion. -/
theorem finite_neighbors [∀ i, Finite (F i)] (v : Vertex F) :
    Finite ((graph F).neighborSet v) := by
  obtain ⟨a, ha⟩ := exists_smul_base F v
  let b := a • base F (!v.type)
  have hb : (graph F).Adj v b := by
    rw [← ha]
    exact (translationGraphIso F a).map_adj_iff.mpr
      ⟨by change v.type ≠ !v.type; cases v.type <;> decide,
        incident_base F v.type (!v.type)⟩
  let f : stabilizer F v → (graph F).neighborSet v := fun g =>
    localAction F v g ⟨b, hb⟩
  apply Finite.of_surjective f
  intro w
  obtain ⟨g, hg, he⟩ := locally_transitive F hb w.property
  exact ⟨⟨g, hg⟩, Subtype.ext he⟩

/-- The intrinsic core of the local kernel equals the vertex core when the edge
contains a vertex Sylow subgroup. This does not identify the kernel with its core. -/
theorem core_ballKernel_one {v w : Vertex F} (h : (graph F).Adj v w)
    (T : Sylow 2 (stabilizer F v))
    (hT : (T : Subgroup (stabilizer F v)).map (stabilizer F v).subtype ≤
      stabilizer F w) :
    (ballKernel F v 1).pCoreIn 2 = (stabilizer F v).pCoreIn 2 := by
  rw [ballKernel_one_eq_map_normalCore F h]
  apply AmalgamLocalCores.vertex_core_eq_kernel_core
  exact le_inf (map_subtype_le _) hT

end Theory.GroupTheory.AmalgamGraph
