module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.SuzukiRigidity.OppositeScales.FourLines
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation

/-!
# The opposite central Suzuki braid

The two type V words at parameters `(0, 1)` lie in the binary middle-node
Levi: their nonsimple root factors are conjugates of simple root generators
by the corresponding Weyl words. In the faithful action of this entire Levi
on four half-root lines, their matrices satisfy the alternating relation of
length five. Faithfulness lifts this equality to the actual split F₄ group.

Embedding the binary coefficient field into each Ree coefficient field then
transports the relation. The root curves are natural under this embedding
because their divided-power coefficients are integral. Thus the conclusion
is an unconditional identity of the literal ambient root words for every `m`.

Source: GLS3, Table 2.4 type V and §§2.4–2.5,
`refs/KGroup/GLS3/chapter2.tex`. The binary Levi comparison is the split B₂
calculation underlying Aschbacher–Smith F.1.12(I)(5), printed pp.263–264
(PDF pp.274–275) of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.SuzukiRigidity.OppositeScales
open Parabolics.BinarySuzuki
namespace CentralBraidProof
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private abbrev middleSimple (i : Fin 2) : typeF4RootPairing_base.support :=
  typeF4RootPairing_baseEquiv (if i = 0 then 1 else 2)

private def simpleIndex (positive : Bool) (i : Fin 2) : Fin 4 :=
  if positive then (if i = 0 then 0 else 1) else (if i = 0 then 2 else 3)

private def simple (positive : Bool) (i : Fin 2) : splitLevi :=
  MatrixIdentification.splitGenerator (simpleIndex positive i)

private theorem simple_val (positive : Bool) (i : Fin 2) :
    (simple positive i).val.val =
      F4Chevalley.rootCurve (signedRoot positive (middleSimple i)) (1 : CoefficientField 0) := by
  cases positive <;> fin_cases i <;> rfl

private def weyl (i : Fin 2) : splitLevi :=
  simple true i * simple false i * simple true i

private theorem weyl_val (i : Fin 2) :
    (weyl i).val.val = WordRelations.titsUnit (S := CoefficientField 0) [middleSimple i] := by
  simp only [weyl, Subgroup.coe_mul, simple_val, WordRelations.titsUnit_cons,
    WordRelations.titsUnit_nil, mul_one, CharTwo.neg_eq, signedRoot,
    Bool.false_eq_true, ↓reduceIte]

private theorem reflected_pos (i j : Fin 2) (hij : i ≠ j) :
    typeF4RootPairing_base.IsPos
      (typeF4RootPairing.reflectionPerm (middleSimple i) (middleSimple j)) := by
  apply (typeF4RootPairing_base.isPos_of_mem_support (middleSimple j).property).reflectionPerm
    (middleSimple i).property
  intro h
  have he := typeF4RootPairing_baseEquiv.injective (Subtype.ext h)
  fin_cases i <;> fin_cases j <;> first
  | exact hij rfl
  | contradiction

private theorem reflected_val (positive : Bool) (i j : Fin 2) (hij : i ≠ j) :
    (weyl i * simple positive j * (weyl i)⁻¹).val.val =
      F4Chevalley.rootCurve (signedRoot positive
        (typeF4RootPairing.reflectionPerm (middleSimple i) (middleSimple j)))
          (1 : CoefficientField 0) := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, weyl_val, simple_val]
  cases positive
  · exact (WordRelations.rootCurve_neg_of_pos_transport _ (reflected_pos i j hij)
      [middleSimple i] (middleSimple j) rfl 1).symm
  · exact (WordRelations.rootCurve_of_pos_transport _ (reflected_pos i j hij)
      [middleSimple i] (middleSimple j) rfl 1).symm

private def central (positive : Bool) : splitLevi :=
  (weyl 1 * simple positive 0 * (weyl 1)⁻¹) *
    (weyl 0 * simple positive 1 * (weyl 0)⁻¹)

private theorem central_val (positive : Bool) :
    (central positive).val = suzukiWord 0 positive 0 1 := by
  apply Subtype.ext
  change (weyl 1 * simple positive 0 * (weyl 1)⁻¹).val.val *
    (weyl 0 * simple positive 1 * (weyl 0)⁻¹).val.val = _
  rw [reflected_val positive 1 0 (by decide), reflected_val positive 0 1 (by decide)]
  simp only [suzukiWord_coe, map_zero, map_one,
    zero_mul, zero_add, F4Chevalley.rootCurve_zero, one_mul]
  rfl

private def weylMatrix (i : Fin 2) : Matrix (Fin 4) (Fin 4) (CoefficientField 0) :=
  if i = 0 then !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]
  else !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]

private theorem weylMatrix_sq (i : Fin 2) : weylMatrix i * weylMatrix i = 1 := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [weylMatrix, Matrix.mul_apply, Fin.sum_univ_four]

private def weylUnit (i : Fin 2) : MatrixIdentification.BinaryGL where
  val := weylMatrix i
  inv := weylMatrix i
  val_inv := weylMatrix_sq i
  inv_val := weylMatrix_sq i

private theorem weyl_image (i : Fin 2) :
    MatrixIdentification.splitLeviRepresentation (weyl i) = weylUnit i := by
  simp only [weyl, simple, map_mul, MatrixIdentification.splitLeviRepresentation_generator]
  apply Units.ext
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [simpleIndex, MatrixIdentification.matrixGenerator,
      MatrixIdentification.generatorMatrix, weylUnit, weylMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

private def centralMatrix (positive : Bool) : Matrix (Fin 4) (Fin 4) (CoefficientField 0) :=
  if positive then !![1,0,1,1; 0,1,0,1; 0,0,1,0; 0,0,0,1]
  else !![1,0,0,0; 0,1,0,0; 1,0,1,0; 1,1,0,1]

private theorem central_image (positive : Bool) :
    (MatrixIdentification.splitLeviRepresentation (central positive)).val =
      centralMatrix positive := by
  simp only [central, map_mul, map_inv, weyl_image, simple,
    MatrixIdentification.splitLeviRepresentation_generator]
  ext j k
  cases positive <;> fin_cases j <;> fin_cases k <;>
    simp [simpleIndex, MatrixIdentification.matrixGenerator,
      MatrixIdentification.generatorMatrix, weylUnit, weylMatrix, centralMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

private theorem central_braid_binary :
    fivefold (suzukiWord 0 true 0 1) (suzukiWord 0 false 0 1) =
      fivefold (suzukiWord 0 false 0 1) (suzukiWord 0 true 0 1) := by
  have h : fivefold (central true) (central false) =
      fivefold (central false) (central true) := by
    apply MatrixIdentification.splitLeviRepresentation_injective
    apply Units.ext
    simp only [fivefold, map_mul, Units.val_mul, central_image]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [centralMatrix, Matrix.mul_apply, Fin.sum_univ_four,
        CharTwo.add_self_eq_zero]
  simpa only [fivefold, Subgroup.coe_mul, central_val] using congrArg Subtype.val h

private def binaryFieldMap (m : ℕ) : CoefficientField 0 →+* CoefficientField m :=
  (algebraMap (ZMod 2) (CoefficientField m)).comp
    (GaloisField.equivZmodP 2).toRingEquiv.toRingHom

private def binaryUnitsMap (m : ℕ) : MatrixUnits 0 →* MatrixUnits m :=
  Units.map (binaryFieldMap m).mapMatrix.toMonoidHom

private theorem binaryUnitsMap_root (m : ℕ) (r : F4Chevalley.Root)
    (t : CoefficientField 0) :
    binaryUnitsMap m (F4Chevalley.rootCurve r t) =
      F4Chevalley.rootCurve r (binaryFieldMap m t) := by
  apply Units.ext
  change (F4Chevalley.rootCurve r t).val.map (binaryFieldMap m) = _
  rw [F4Chevalley.rootCurve_matrix_formula, F4Chevalley.rootCurve_matrix_formula]
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    specializeMatrix, Matrix.one_apply, apply_ite (binaryFieldMap m)]

private theorem binaryUnitsMap_central (m : ℕ) (positive : Bool) :
    binaryUnitsMap m (suzukiWord 0 positive 0 1).val =
      (suzukiWord m positive 0 1).val := by
  simp only [suzukiWord_coe, map_zero, map_one, zero_mul, zero_add,
    F4Chevalley.rootCurve_zero, one_mul, map_mul, binaryUnitsMap_root]

end CentralBraidProof

open CentralBraidProof in
/-- The literal opposite central Suzuki words at parameter one satisfy the
alternating braid of length five in the actual split F₄ group. -/
theorem central_fivefold (m : ℕ) :
    fivefold (suzukiWord m true 0 1) (suzukiWord m false 0 1) =
      fivefold (suzukiWord m false 0 1) (suzukiWord m true 0 1) := by
  apply Subtype.ext
  have h := congrArg (fun x : SplitGroup 0 => binaryUnitsMap m x.val) central_braid_binary
  simpa only [fivefold, Subgroup.coe_mul, map_mul, binaryUnitsMap_central] using h

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.SuzukiRigidity.OppositeScales
end
