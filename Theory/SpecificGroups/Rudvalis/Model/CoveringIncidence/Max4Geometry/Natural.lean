module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Basic
public import Theory.Representation.PSL3Two.SmallModules

/-!
# The marked natural module of Rudvalis max4

The three published commuting involutions form a basis: their linear span is
the whole marked eight-group, and both spaces have eight elements. These
coordinates turn every actual conjugation automorphism into its binary matrix.
The resulting SL3(2) actor is an equivalence from the literal max4/P quotient;
its projection formula and the intertwining identity hold for every element.

Once the independent center calculation identifies Z(P) with the marked
eight-group, the same coordinates identify the actual center action with W.
This conditional application does not establish that center calculation or
the other, Steinberg, module factor.

Source: Aschbacher--Smith I.2.2(7), printed pp.412--413. The original ATLAS
words and left-conjugation convention are inherited unchanged.
-/

public section

open Subgroup
open Rudvalis Rudvalis.SylowOvergroups Rudvalis.CoreQuotients
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open scoped IsMulCommutative
namespace Rudvalis.CoveringIncidence

local instance : IsElementaryAbelian 2 (elementary 2) :=
  RankOneEightCharacteristic.elementary_two_elementary

@[expose] public def markedBasis (i : Fin 3) : elementary 2 :=
  ⟨RankOneEightCharacteristic.basis i, RankOneEightCharacteristic.basis_mem i⟩

private theorem markedBasis_closure : closure (Set.range markedBasis) = ⊤ := by
  apply map_injective (elementary 2).subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp]
  rw [← MonoidHom.range_eq_map, range_subtype]
  exact RankOneEightCharacteristic.closure_basis

public noncomputable def markedFromVector :
    BinaryLinearThree.Vector →ₗ[ZMod 2] Additive (elementary 2) :=
  Fintype.linearCombination (ZMod 2) (fun i => Additive.ofMul (markedBasis i))

public theorem markedFromVector_single (i : Fin 3) :
    markedFromVector (Pi.single i 1) = Additive.ofMul (markedBasis i) := by
  simp [markedFromVector, Fintype.linearCombination_apply_single]

private theorem markedFromVector_surjective : Function.Surjective markedFromVector := by
  let f : Multiplicative BinaryLinearThree.Vector →* elementary 2 :=
    markedFromVector.toAddMonoidHom.toMultiplicativeLeft
  have hr : f.range = ⊤ := by
    apply top_unique
    rw [← markedBasis_closure]
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨Multiplicative.ofAdd (Pi.single i 1), markedFromVector_single i⟩
  exact MonoidHom.range_eq_top.mp hr

public noncomputable def markedCoordinates :
    Additive (elementary 2) ≃ₗ[ZMod 2] BinaryLinearThree.Vector :=
  (LinearEquiv.ofBijective markedFromVector
    ((Nat.bijective_iff_surjective_and_card markedFromVector).mpr
      ⟨markedFromVector_surjective, by
        change Nat.card BinaryLinearThree.Vector = Nat.card (elementary 2)
        rw [RankOneEightCharacteristic.elementary_two_card]
        change Nat.card (Fin 3 → ZMod 2) = 8
        simp⟩)).symm

public theorem markedCoordinates_basis (i : Fin 3) :
    markedCoordinates (Additive.ofMul (markedBasis i)) = Pi.single i 1 := by
  apply markedCoordinates.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (markedFromVector_single i).symm

private noncomputable def markedAutLinear :
    MulAut (elementary 2) ≃* (Additive (elementary 2) ≃ₗ[ZMod 2] Additive (elementary 2)) where
  toFun a := { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
  invFun a := MulEquiv.toAdditive.symm a.toAddEquiv
  left_inv a := by ext; rfl
  right_inv a := by ext; rfl
  map_mul' a b := by ext; rfl

private noncomputable def markedAutGL : MulAut (elementary 2) ≃* Matrix.PSL3Two.GeneralLinear :=
  markedAutLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive (elementary 2))).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv markedCoordinates).trans
        Matrix.GeneralLinearGroup.toLin.symm))

public noncomputable def markedAutSL : MulAut (elementary 2) ≃* BinaryLinearThree.Group :=
  markedAutGL.trans Matrix.PSL3Two.equivGL.symm

public theorem markedAutSL_apply (a : MulAut (elementary 2)) (x : elementary 2) :
    BinaryLinearThree.W (markedAutSL a) (markedCoordinates (Additive.ofMul x)) =
      markedCoordinates (Additive.ofMul (a x)) := by
  have hgl : Matrix.PSL3Two.equivGL (markedAutSL a) = markedAutGL a :=
    Matrix.PSL3Two.equivGL.apply_symm_apply _
  have hv := congrArg (fun g : Matrix.PSL3Two.GeneralLinear =>
    (Matrix.GeneralLinearGroup.toLin g : Module.End (ZMod 2) BinaryLinearThree.Vector)
      (markedCoordinates (Additive.ofMul x))) hgl
  rw [Matrix.PSL3Two.equivGL_apply] at hv
  change BinaryLinearThree.W (markedAutSL a) (markedCoordinates (Additive.ofMul x)) = _ at hv
  rw [hv]
  change (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.congrLinearEquiv markedCoordinates
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive (elementary 2))).symm
        (markedAutLinear a)))) : Module.End (ZMod 2) BinaryLinearThree.Vector) _ = _
  rw [MulEquiv.apply_symm_apply]
  change markedCoordinates ((markedAutLinear a) (markedCoordinates.symm
    (markedCoordinates (Additive.ofMul x)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

public noncomputable def max4NaturalActor :
    (max4 ⧸ pCore 2 max4) ≃* BinaryLinearThree.Group :=
  max4QuotientEquiv.trans (eightAutEquivPSL.symm.trans markedAutSL)

public theorem max4NaturalActor_mk (g : max4) :
    max4NaturalActor (QuotientGroup.mk' (pCore 2 max4) g) = markedAutSL (max4EightAction g) := by
  change markedAutSL (eightAutEquivPSL.symm (max4QuotientEquiv _)) = _
  rw [max4QuotientEquiv_mk]
  change markedAutSL (eightAutEquivPSL.symm (eightAutEquivPSL _)) = _
  rw [MulEquiv.symm_apply_apply]

public theorem max4_marked_natural (g : max4) (x : elementary 2) :
    BinaryLinearThree.W (max4NaturalActor (QuotientGroup.mk' (pCore 2 max4) g))
        (markedCoordinates (Additive.ofMul x)) =
      markedCoordinates (Additive.ofMul (max4EightAction g x)) := by
  rw [max4NaturalActor_mk]
  exact markedAutSL_apply _ _

end Rudvalis.CoveringIncidence
namespace Rudvalis.CoveringIncidence
open Subgroup SylowOvergroups CoreQuotients
open SylowOvergroups.RadicalCoverage.LocalCover

local instance : IsElementaryAbelian 2 (elementary 2) :=
  RankOneEightCharacteristic.elementary_two_elementary

public noncomputable def markedCoordinatesMul :
    elementary 2 ≃* Multiplicative BinaryLinearThree.Vector :=
  markedCoordinates.toAddEquiv.toMultiplicativeRight

public noncomputable def max4CenterCoordinates (hcenter : max4CoreCenter = elementary 2) :
    center max4Core ≃* Multiplicative BinaryLinearThree.Vector :=
  (centerEquivMarked hcenter).trans markedCoordinatesMul

public theorem max4_center_natural (hcenter : max4CoreCenter = elementary 2)
    (g : max4) (x : center max4Core) :
    (max4CenterCoordinates hcenter (max4CenterAction g x)).toAdd =
      BinaryLinearThree.W (max4NaturalActor (QuotientGroup.mk' (pCore 2 max4) g))
        (max4CenterCoordinates hcenter x).toAdd := by
  change markedCoordinates (Additive.ofMul (centerEquivMarked hcenter (max4CenterAction g x))) = _
  rw [centerEquivMarked_action]
  exact (max4_marked_natural g (centerEquivMarked hcenter x)).symm

end Rudvalis.CoveringIncidence
