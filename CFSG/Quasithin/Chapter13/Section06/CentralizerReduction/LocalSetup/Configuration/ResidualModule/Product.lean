module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.Quotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.MovedCoordinates
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The direct product inside the actual conjugate span

Conjugation equivariance identifies every residual commutator with a coordinate
difference. Lifting the cubic and its square gives the two generators of the
moved plane, so [V,Lᵥ] is exactly its ambient image. The coordinate splitting
then gives Vᵥ = ⟨v⟩[V,Lᵥ], disjoint factors and commutation. The resulting
isomorphism is the natural product map, not merely a cardinality comparison.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.926.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry ResidualCoordinates
open scoped commutatorElement IsMulCommutative
variable {G : Type*} [Group G] {L V : Subgroup G} (s : Marking L V)

theorem residual_commutator_formula (l : Lv L (markedV s)) (x : Space) :
    ⁅(l : G), s.map (Multiplicative.ofAdd x)⁆ =
      s.map (Multiplicative.ofAdd (act (residualAction s l) x - x)) := by
  have he := s.equivariant (inclusion (residual_le_L s) l) x
  change MulAut.conj (l : G) (s.map (Multiplicative.ofAdd x)) =
    s.map (Multiplicative.ofAdd (act (residualAction s l) x)) at he
  rw [ofAdd_sub, map_div, div_eq_mul_inv, ← he]
  rfl

theorem residual_commutator_le_moved :
    ⁅V, Lv L (markedV s)⁆ ≤ moved.map s.map := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl x hx
  obtain ⟨y, rfl⟩ := s.range_eq.symm ▸ hx
  change ⁅(⟨l, hl⟩ : Lv L (markedV s)).val, s.map (Multiplicative.ofAdd y.toAdd)⁆ ∈ _
  rw [residual_commutator_formula]
  exact mem_map.mpr ⟨_, difference_mem (residualCubicAction s ⟨l, hl⟩) y.toAdd, rfl⟩

variable [Finite G]

theorem mapped_difference_mem_commutator (g : cubicGroup) (x : Space) :
    s.map (Multiplicative.ofAdd (act g.val x - x)) ∈ ⁅V, Lv L (markedV s)⁆ := by
  obtain ⟨l, hl⟩ := residualCubicAction_surjective s g
  have he : residualAction s l = g.val := congrArg Subtype.val hl
  rw [← he, ← residual_commutator_formula]
  rw [commutator_comm]
  exact commutator_mem_commutator l.property (map_mem s _)

theorem residual_commutator_eq_moved : ⁅V, Lv L (markedV s)⁆ = moved.map s.map := by
  apply le_antisymm (residual_commutator_le_moved s)
  have h1 := mapped_difference_mem_commutator s ⟨cubic, cubic_mem⟩ z
  have h2 := mapped_difference_mem_commutator s ⟨cubic ^ 2, cubicGroup.pow_mem cubic_mem 2⟩ z
  change s.map (Multiplicative.ofAdd deltaOne) ∈ _ at h1
  change s.map (Multiplicative.ofAdd deltaTwo) ∈ _ at h2
  rintro x ⟨y, hy, rfl⟩
  change s.map (Multiplicative.ofAdd y.toAdd) ∈ _
  rcases moved_cases y.toAdd hy with he | he | he | he <;> rw [he]
  · exact (map_one s.map) ▸ one_mem _
  · exact h1
  · exact h2
  · rw [ofAdd_add, map_mul]
    exact mul_mem h1 h2

theorem Vv_eq_line_sup_commutator :
    Vv L (markedZ s) (markedV s) = zpowers (markedV s) ⊔ ⁅V, Lv L (markedV s)⁆ := by
  rw [Vv_eq_plane s, plane_eq_line_sup_moved, Subgroup.map_sup,
    MonoidHom.map_zpowers, residual_commutator_eq_moved s]
  rfl

theorem line_disjoint_commutator : Disjoint (zpowers (markedV s)) ⁅V, Lv L (markedV s)⁆ := by
  rw [residual_commutator_eq_moved s]
  have hh := Subgroup.disjoint_map s.injective line_disjoint_moved
  simpa only [MonoidHom.map_zpowers, markedV] using hh

theorem residual_commutator_le_module : ⁅V, Lv L (markedV s)⁆ ≤ V := by
  rw [residual_commutator_eq_moved s]
  rintro x ⟨y, _, rfl⟩
  exact map_mem s y

theorem line_commutes_commutator (x : zpowers (markedV s)) (y : ↥(⁅V, Lv L (markedV s)⁆ : Subgroup G)) :
    Commute ((zpowers (markedV s)).subtype x) ((⁅V, Lv L (markedV s)⁆ : Subgroup G).subtype y) := by
  let := module_abelian s
  exact setLike_mul_comm ((zpowers_le.mpr (map_mem s (Multiplicative.ofAdd v))) x.property)
    (residual_commutator_le_module s y.property)

/-- The natural multiplication map from the two actual ambient subgroups. -/
def spanProductMap : zpowers (markedV s) × ↥(⁅V, Lv L (markedV s)⁆ : Subgroup G) →* G :=
  (zpowers (markedV s)).subtype.noncommCoprod (⁅V, Lv L (markedV s)⁆ : Subgroup G).subtype
    (line_commutes_commutator s)

theorem spanProductMap_injective : Function.Injective (spanProductMap s) := by
  apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
  refine ⟨Subtype.val_injective, Subtype.val_injective, ?_⟩
  simpa only [range_subtype] using line_disjoint_commutator s

theorem spanProductMap_range : (spanProductMap s).range = Vv L (markedZ s) (markedV s) := by
  rw [spanProductMap, MonoidHom.noncommCoprod_range, range_subtype, range_subtype,
    ← Vv_eq_line_sup_commutator s]

noncomputable def spanProductEquiv :
    zpowers (markedV s) × ↥(⁅V, Lv L (markedV s)⁆ : Subgroup G) ≃* Vv L (markedZ s) (markedV s) :=
  (MonoidHom.ofInjective (spanProductMap_injective s)).trans
    (MulEquiv.subgroupCongr (spanProductMap_range s))

@[simp] theorem spanProductEquiv_apply (x : zpowers (markedV s)) (y : ↥(⁅V, Lv L (markedV s)⁆ : Subgroup G)) :
    (spanProductEquiv s (x, y) : G) = (x : G) * (y : G) := rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
