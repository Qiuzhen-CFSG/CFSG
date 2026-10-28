module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.PointHyperplane
public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.ModelReduction
public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.RankOneBlock
public import Theory.Representation.G2BinaryNondegeneratePlane.ExtraspecialCubic

/-!
# The literal perpendicular subgroup in the plane-centralizer argument

The natural coordinate chart pulls the perpendicular four-space back to a
subgroup of the original chosen module. Its equivalence with the model is a
multiplicative equivalence, and its cubic action is actual ambient conjugation.
Consequently the rank-one endpoint can be applied to a component containing
this subgroup, with the component inclusion and Sylow centralization retained.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890, especially (*).
The earlier component construction and block placement are not asserted here.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Atlas.G2.Natural.BinaryNondegeneratePlane
variable {G : Type*} [Group G] {V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The subgroup of the original module cut out by a model subspace. -/
def coordinateGroup (E : Additive V ≃ₗ[K] W) (P : Submodule K W) : Subgroup G :=
  UnitaryGeometry.ambientGroup (P.comap E.toLinearMap)

theorem coordinateGroup_le (E : Additive V ≃ₗ[K] W) (P : Submodule K W) :
    coordinateGroup E P ≤ V := UnitaryGeometry.ambientGroup_le_module _

@[simp] theorem mem_coordinateGroup (E : Additive V ≃ₗ[K] W)
    (P : Submodule K W) (v : Additive V) :
    v.toMul.val ∈ coordinateGroup E P ↔ E v ∈ P := by
  change v.toMul.val ∈ (UnitaryGeometry.subgroupSpace.symm
    (P.comap E.toLinearMap)).map V.subtype ↔ _
  constructor
  · rintro ⟨w, hw, he⟩
    have hwv : Additive.ofMul w = v := congrArg Additive.ofMul (Subtype.ext he)
    exact hwv ▸ hw
  · intro hv
    exact ⟨v.toMul, hv, rfl⟩

/-- Coordinate transport retains multiplication and the original inclusion. -/
def coordinateEquiv (E : Additive V ≃ₗ[K] W) (P : Submodule K W) :
    coordinateGroup E P ≃* Multiplicative P where
  toFun x := Multiplicative.ofAdd
    ⟨E (Additive.ofMul ⟨x.val, coordinateGroup_le E P x.property⟩),
      (mem_coordinateGroup E P _).mp x.property⟩
  invFun w := ⟨(E.symm w.toAdd.val).toMul.val,
    (mem_coordinateGroup E P _).mpr (by
      simpa only [LinearEquiv.apply_symm_apply] using w.toAdd.property)⟩
  left_inv x := by simp
  right_inv w := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact E.map_add
      (Additive.ofMul (⟨x.val, coordinateGroup_le E P x.property⟩ : V))
      (Additive.ofMul (⟨y.val, coordinateGroup_le E P y.property⟩ : V))

theorem coordinateGroup_space (E : Additive V ≃ₗ[K] W) (P : Submodule K W) :
    pointCoordinateSubspace E (coordinateGroup E P) = P := by
  ext w
  obtain ⟨v, rfl⟩ := E.surjective w
  rw [mem_pointCoordinateSubspace, mem_coordinateGroup]

/-- The actual subgroup denoted by l-perpendicular in the source. -/
def perpendicular (E : Additive V ≃ₗ[K] W) : Subgroup G :=
  coordinateGroup E (form.orthogonal plane)

theorem perpendicular_le (E : Additive V ≃ₗ[K] W) : perpendicular E ≤ V :=
  coordinateGroup_le E _

theorem perpendicular_card (E : Additive V ≃ₗ[K] W) :
    Nat.card (perpendicular E) = 16 := by
  rw [perpendicular, Nat.card_congr (coordinateEquiv E _).toEquiv]
  change Nat.card (form.orthogonal plane) = 16
  rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_zmod, finrank_orthogonal]
  decide

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
