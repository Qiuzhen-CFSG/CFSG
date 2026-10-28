module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Actual.Checks
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.StandardPair

/-!
# Realizing the full binary G₂ word tables in the original parabolic pair

The positive row words lie in the original short and long root parabolics.
Their checked matrix actions distinguish all 192 rows on each side; the
parabolic orders therefore make both maps bijections. Word induction gives
the actual multiplication laws. The 64 overlap rows have the same matrices
on both sides. Their injectivity and the order of the entire common Sylow
subgroup give the middle bijection, with both literal inclusion squares.

This supplies the actual-coordinate premise of finite overlap-twist
factorization; no twist-factorization or model-comparison premise is used.
Source application: Aschbacher--Smith F.1.12(I)(3), q = 2, pp.262--263.
Root coordinates: Gerald Höhn and the ATLAS contributors, ATLAS Research
and Attribution License 1.0 (`LICENSES/ATLAS.txt`).
-/

public section
open Atlas.G2 Atlas.SplitOctonion
open Atlas.G2.BinaryParabolicPair Atlas.G2.BinaryCore Atlas.G2.LieParabolicSetup
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists
open _root_.Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Actual

private theorem common_mem_unipotent : commonGenerator ∈ unipotent := by
  have h := unipotentProduct_mem (![0,0,1,0,1,1] : Fin 6 → ZMod 2)
  simpa [unipotentProduct, commonGenerator] using h

private theorem rootC_mem_unipotent : (rootC 1 : Model (ZMod 2)) ∈ unipotent :=
  Subgroup.subset_closure (by simp)

private theorem leftGenerators_mem (b : Fin 3) : leftGenerators b ∈ firstParabolic := by
  fin_cases b
  · exact unipotent_le_firstParabolic common_mem_unipotent
  · exact cubicActor_mem
  · exact unipotent_le_firstParabolic rootC_mem_unipotent

private theorem rightGenerators_mem (b : Fin 3) : rightGenerators b ∈ secondParabolic := by
  fin_cases b
  · exact unipotent_le_parabolic common_mem_unipotent
  · exact movingActor_mem
  · exact unipotent_le_parabolic rootC_mem_unipotent

private def leftRow (i : Fin 192) : firstParabolic :=
  ⟨leftCoordinates.row leftGenerators i,
    leftCoordinates.row_mem leftGenerators firstParabolic leftGenerators_mem i⟩

private def rightRow (i : Fin 192) : secondParabolic :=
  ⟨rightCoordinates.row rightGenerators i,
    rightCoordinates.row_mem rightGenerators secondParabolic rightGenerators_mem i⟩

private theorem leftRow_injective : Function.Injective leftRow := by
  intro i j h
  exact left_action.row_injective (congrArg Subtype.val h)

private theorem rightRow_injective : Function.Injective rightRow := by
  intro i j h
  exact right_action.row_injective (congrArg Subtype.val h)

private noncomputable def leftEquiv : Fin 192 ≃ firstParabolic :=
  Equiv.ofBijective leftRow
    (leftRow_injective.bijective_of_nat_card_le (by rw [card_firstParabolic, Nat.card_fin]))

private noncomputable def rightEquiv : Fin 192 ≃ secondParabolic :=
  Equiv.ofBijective rightRow
    (rightRow_injective.bijective_of_nat_card_le (by rw [secondParabolic_card, Nat.card_fin]))

private theorem overlap_rows (i : Fin 64) :
    (leftRow (leftOverlap i)).val = (rightRow (rightOverlap i)).val := by
  apply BinaryAmalgamBound.Actual.model_ext
  intro c
  change (leftCoordinates.row leftGenerators _).val (basisVector c) =
    (rightCoordinates.row rightGenerators _).val (basisVector c)
  rw [left_action.row_action, right_action.row_action]
  exact congrArg (fun a => column a c) (overlap_labels i)

private def middleRow (i : Fin 64) : (commonSylow : Subgroup (Model (ZMod 2))) :=
  ⟨(leftRow (leftOverlap i)).val, by
    change (leftRow (leftOverlap i)).val ∈ unipotent
    rw [← parabolic_intersection]
    exact ⟨(leftRow (leftOverlap i)).prop,
      (overlap_rows i).symm ▸ (rightRow (rightOverlap i)).prop⟩⟩

private theorem middleRow_injective : Function.Injective middleRow := by
  intro i j h
  apply left_overlap_injective
  apply leftRow_injective
  exact Subtype.ext (congrArg
    (fun z : (commonSylow : Subgroup (Model (ZMod 2))) => z.val) h)

private noncomputable def middleEquiv : Fin 64 ≃
    (commonSylow : Subgroup (Model (ZMod 2))) :=
  Equiv.ofBijective middleRow
    (middleRow_injective.bijective_of_nat_card_le (by
      change Nat.card (unipotent (K := ZMod 2)) ≤ Nat.card (Fin 64)
      rw [card_unipotent_binary, Nat.card_fin]))

private theorem middleRow_mul (i j : Fin 64) :
    middleRow (middleMul i j) = middleRow i * middleRow j := by
  apply Subtype.ext
  change leftCoordinates.row leftGenerators (leftOverlap (middleMul i j)) =
    leftCoordinates.row leftGenerators (leftOverlap i) *
      leftCoordinates.row leftGenerators (leftOverlap j)
  rw [left_overlap_mul]
  exact left_action.row_mul _ _

/-- The published 192/64/192 tables realize both actual parabolics and their full overlap. -/
noncomputable def fullConcreteRealization : table.Realization concreteAmalgam where
  left := leftEquiv
  middle := middleEquiv
  right := rightEquiv
  left_mul i j := Subtype.ext (left_action.row_mul i j)
  middle_mul := middleRow_mul
  right_mul i j := Subtype.ext (right_action.row_mul i j)
  left_overlap _ := rfl
  right_overlap i := Subtype.ext (overlap_rows i).symm

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists
