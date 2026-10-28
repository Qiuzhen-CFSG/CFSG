module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.LowerBound.FixedObject
public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.Bounds

/-!
# A spanning-tree certificate for the fixed-plane orbit

Each nonroot row basis is reached from an earlier basis by one standard linear
generator and a square change of row coordinates. Independent rows make this a
subspace equality. Induction on the parent indices constructs representatives
in the actual projective model, with inverse generators because these are row
actions. Distinct row spans then give the lower bound for the local subgroup.
Only a spanning tree is required; no closure or stabilizer identification is
assumed. See `../source/README.md` for the invariant basis and matrix sources.
-/

@[expose] public section

namespace ONan.OrderCertificate
open Matrix

/-- The linear lifts of the two indexed projective generators. -/
def linearCosetGenerator : Bool → GeneralLinearGroup (Fin 45) (ZMod 7)
  | false => linearA
  | true => linearB

/-- These are lifts in the specified matrix model. -/
lemma linearCosetGenerator_projective (b : Bool) :
    ProjGenLinGroup.mk (linearCosetGenerator b) = (cosetGenerators b).val := by
  cases b <;> rfl

/-- A concrete row-matrix identity supplies an orbit edge. -/
lemma inverse_generator_smul_range (b : Bool)
    (W V : Matrix (Fin 8) (Fin 45) (ZMod 7))
    (C : Matrix (Fin 8) (Fin 8) (ZMod 7))
    (hW : Function.Injective W.vecMul)
    (h : W * (linearCosetGenerator b : Matrix (Fin 45) (Fin 45) (ZMod 7)) = C * V) :
    (cosetGenerators b)⁻¹ • LinearMap.range W.vecMulLinear =
      LinearMap.range V.vecMulLinear := by
  rw [rowSpace_smul_of_lift _ ((linearCosetGenerator b)⁻¹) (by
    change (cosetGenerators b).val⁻¹ = ProjGenLinGroup.mk ((linearCosetGenerator b)⁻¹)
    rw [map_inv, linearCosetGenerator_projective])]
  exact RowSpaces.inv_smul_range_of_mul W V _ C hW h

/-- Data and checked identities for 122,760 distinct translates of the fixed plane. -/
structure FixedPlaneOrbitTree where
  rows : Fin 122760 → Matrix (Fin 8) (Fin 45) (ZMod 7)
  root_rows : rows 0 = fixedPlaneRows
  parent : Fin 122760 → Fin 122760
  parent_lt : ∀ i, i ≠ 0 → parent i < i
  letter : Fin 122760 → Bool
  coefficient : Fin 122760 → Matrix (Fin 8) (Fin 8) (ZMod 7)
  edge : ∀ i, i ≠ 0 → rows (parent i) *
    (linearCosetGenerator (letter i) : Matrix (Fin 45) (Fin 45) (ZMod 7)) =
      coefficient i * rows i
  independent : ∀ i, Function.Injective (rows i).vecMul
  distinct : Function.Injective (fun i => LinearMap.range (rows i).vecMulLinear)

namespace FixedPlaneOrbitTree
/-- Every node represents a translate of the original fixed plane. -/
lemma exists_representative (T : FixedPlaneOrbitTree) (i : Fin 122760) :
    ∃ g : Model, g • fixedPlane = LinearMap.range (T.rows i).vecMulLinear := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : i = 0
    · subst i
      exact ⟨1, by rw [one_smul, T.root_rows]; rfl⟩
    · obtain ⟨g, hg⟩ := ih (T.parent i) (T.parent_lt i hi)
      refine ⟨(cosetGenerators (T.letter i))⁻¹ * g, ?_⟩
      rw [mul_smul, hg]
      exact inverse_generator_smul_range _ _ _ _ (T.independent _) (T.edge i hi)

/-- Choose the representatives whose existence is proved by tree induction. -/
noncomputable def repr (T : FixedPlaneOrbitTree) (i : Fin 122760) : Model :=
  (T.exists_representative i).choose

/-- The chosen representative reaches the node specified by the row basis. -/
lemma repr_smul (T : FixedPlaneOrbitTree) (i : Fin 122760) :
    T.repr i • fixedPlane = LinearMap.range (T.rows i).vecMulLinear :=
  (T.exists_representative i).choose_spec

/-- Distinct row spans imply distinct translates. -/
lemma repr_injective (T : FixedPlaneOrbitTree) :
    Function.Injective (fun i => T.repr i • fixedPlane) := by
  intro i j h
  apply T.distinct
  simpa only [T.repr_smul] using h

/-- A complete tree certificate proves the required numerical index lower bound. -/
lemma index_ge (T : FixedPlaneOrbitTree) : 122760 ≤ localSubgroup.index :=
  localSubgroup_index_ge_of_action fixedPlane fixedPlane_localA fixedPlane_localB
    T.repr T.repr_injective
end FixedPlaneOrbitTree
end ONan.OrderCertificate
