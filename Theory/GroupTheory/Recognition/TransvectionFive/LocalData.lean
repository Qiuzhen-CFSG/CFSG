module

public import Theory.SpecificGroups.BinaryLinear.TransvectionFiveLocal.Defs
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Marked local data for the degree-five transvection recognition

A marking identifies the full centralizer of the actual involution with
the centralizer of I+E₀₄ in SL₅(2). The two elementary root groups and the
two rectangular groups are pulled back along that same marking. Fusion
counts refer to conjugacy in the original ambient group.

The counts (21,21) and (21,45), up to interchange, are the alternatives
in Aschbacher, *Sporadic Groups* (1994), 40.2--40.5, pp.217--219.
Deriving these counts, their normalizer structures, and the uniqueness
theorem 41.6 are separate mathematical obligations. None is asserted by
these definitions. The Held normalizer pattern records only the two
equalities needed to exclude 40.5(3) in Aschbacher--Smith 12.2.27(1).
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive
namespace Model
open BinaryLinear.TransvectionFiveLocal

abbrev row : Subgroup SL := dualFactor
abbrev column : Subgroup SL := naturalFactor
abbrev plane : Subgroup SL := rectangle 2
abbrev threeSpace : Subgroup SL := rectangle 3

theorem row_le_centralizer : row ≤ centralizer :=
  dualFactor_le_kernel.trans (kernel_le_upper.trans upper_le_centralizer)

theorem column_le_centralizer : column ≤ centralizer :=
  naturalFactor_le_kernel.trans (kernel_le_upper.trans upper_le_centralizer)

theorem plane_le_centralizer : plane ≤ centralizer :=
  (rectangle_le_upper 2).trans upper_le_centralizer

theorem threeSpace_le_centralizer : threeSpace ≤ centralizer :=
  (rectangle_le_upper 3).trans upper_le_centralizer

end Model

variable {G : Type*} [Group G]

/-- The whole point centralizer with its distinguished involution. -/
structure MarkedCentralizer (z : G) where
  equiv : centralizer ({z} : Set G) ≃* BinaryLinear.TransvectionFiveLocal.centralizer
  on_point : (equiv ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ :
    BinaryLinear.TransvectionFiveLocal.SL) = BinaryLinear.TransvectionFiveLocal.transvection

namespace MarkedCentralizer
variable {z : G} (F : MarkedCentralizer z)

/-- Pull a model subgroup back into the original ambient group. -/
def pullback (A : Subgroup BinaryLinear.TransvectionFiveLocal.SL) : Subgroup G :=
  ((A.subgroupOf BinaryLinear.TransvectionFiveLocal.centralizer).map
    F.equiv.symm.toMonoidHom).map (centralizer ({z} : Set G)).subtype

abbrev row : Subgroup G := F.pullback Model.row
abbrev column : Subgroup G := F.pullback Model.column
abbrev plane : Subgroup G := F.pullback Model.plane
abbrev threeSpace : Subgroup G := F.pullback Model.threeSpace

theorem pullback_le (A : Subgroup BinaryLinear.TransvectionFiveLocal.SL) :
    F.pullback A ≤ centralizer ({z} : Set G) := map_subtype_le _

/-- Membership in a pulled-back subgroup is tested using the same marked
centralizer equivalence. -/
theorem mem_pullback_iff (A : Subgroup BinaryLinear.TransvectionFiveLocal.SL)
    (x : centralizer ({z} : Set G)) :
    (x : G) ∈ F.pullback A ↔ (F.equiv x : BinaryLinear.TransvectionFiveLocal.SL) ∈ A := by
  constructor
  · rintro ⟨y, ⟨a, ha, hay⟩, hyx⟩
    have hax : F.equiv.symm a = x :=
      hay.trans (Subtype.ext hyx)
    have hea : F.equiv x = a := by rw [← hax, F.equiv.apply_symm_apply]
    rw [hea]
    exact ha
  · intro hx
    exact ⟨x, ⟨F.equiv x, hx, F.equiv.symm_apply_apply x⟩, rfl⟩

include F in
/-- The distinguished point is an involution because the actual
centralizer marking sends it to I+E₀₄. -/
theorem point_orderOf : orderOf z = 2 := by
  let x : centralizer ({z} : Set G) := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  calc
    orderOf z = orderOf x :=
      orderOf_injective (centralizer ({z} : Set G)).subtype Subtype.val_injective x
    _ = orderOf (F.equiv x) := (F.equiv.orderOf_eq x).symm
    _ = orderOf (F.equiv x : BinaryLinear.TransvectionFiveLocal.SL) :=
      (orderOf_injective BinaryLinear.TransvectionFiveLocal.centralizer.subtype
        Subtype.val_injective (F.equiv x)).symm
    _ = 2 := by rw [show (F.equiv x : BinaryLinear.TransvectionFiveLocal.SL) =
      BinaryLinear.TransvectionFiveLocal.transvection from F.on_point]
                exact BinaryLinear.TransvectionFiveLocal.transvection_orderOf

/-- The fusion set is taken in G, not merely in the point centralizer. -/
def fusion (_F : MarkedCentralizer z) (A : Subgroup G) : Set G :=
  {a | a ∈ A ∧ IsConj z a}

/-- The two 21-element fusion sets of the linear case in 40.2--40.5. -/
def LinearFusion : Prop :=
  (F.fusion F.plane).ncard = 21 ∧ (F.fusion F.threeSpace).ncard = 21

/-- The unequal fusion counts of the Mathieu case; the marking may interchange
the two ends of the standard flag. -/
def MathieuFusion : Prop :=
  ((F.fusion F.plane).ncard = 21 ∧ (F.fusion F.threeSpace).ncard = 45) ∨
  ((F.fusion F.plane).ncard = 45 ∧ (F.fusion F.threeSpace).ncard = 21)

/-- The two normalizer equalities in the Held alternative 40.5(3). This
predicate does not assert, or define, an isomorphism with the Held group. -/
def HeldNormalizerPattern : Prop :=
  normalizer (F.row : Set G) = centralizer ({z} : Set G) ∧
  normalizer (F.column : Set G) = centralizer ({z} : Set G)

end MarkedCentralizer

/-- The original point has a distinct G-conjugate in its centralizer's
literal two-core, as required at the start of Section 39. -/
def PointCoreFusion (z : G) : Prop :=
  ∃ g : G, g * z * g⁻¹ ∈ (centralizer ({z} : Set G)).pCoreIn 2 ∧
    g * z * g⁻¹ ≠ z

end Theory.GroupTheory.TransvectionFive
