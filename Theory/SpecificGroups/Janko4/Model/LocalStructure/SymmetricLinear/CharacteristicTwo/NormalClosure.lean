module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Coordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.NormalClosure.Flag
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.NormalClosure.WordEvaluation

/-!
# A normal two-subgroup in the literal max4 carrier

The seed `(first * second^2)^6` acts identically on each diagonal block of the
certified invariant flag. Hence its normal closure, taken inside max4, lies in
the kernel of the diagonal-block action. That normal kernel is a two-group by
its faithful lower triangular binary representation. The imported word proof
also certifies all eleven supplied matrices of the alternating right conjugates.

These discharge the normal-closure and word premises of the independent
`CharacteristicTwo` assembly. No assertion about the quotient, global J₄ order,
ambient simplicity, or a normal elementary eight is required.

Source application: Aschbacher–Smith condition E, printed pp.3–4 and 481–482,
with A.3.12 on pp.47–48. The original seventeen instructions are retained in
`SymmetricLinear/Model/source/J4G1-max4W1`; witness provenance and measured
certificate costs are in `NormalClosure/source/README.md`.
-/

public section

namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo
open GeneratorCertificates NormalClosure

private def flagStart (i : Fin 112) : ℕ :=
  (#[0,4,16,28,31,34,37,40,72,84,87,90,93,96,108] : Array ℕ)[OrderDual.ofDual (flagBlock i)]!

set_option Elab.async false

set_option maxRecDepth 10000 in
private theorem flagStart_le (i j : Fin 112) :
    flagBlock i = flagBlock j → flagStart i ≤ j.val := by
  revert i j
  decide +kernel

set_option maxRecDepth 10000 in
private theorem seed_row_bound : ∀ i : Fin 112,
    ((Coordinates.conjugateRows.get 0).get i ^^^ 2 ^ i.val) < 2 ^ flagStart i := by
  decide +kernel

private theorem seed_diagonal (i j : Fin 112) (hij : flagBlock i = flagBlock j) :
    decodeRows (Coordinates.conjugateRows.get 0) i j = (1 : BinaryMatrix) i j := by
  have hz := Nat.testBit_lt_two_pow ((seed_row_bound i).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (flagStart_le i j hij)))
  have hb : ((Coordinates.conjugateRows.get 0).get i).testBit j.val =
      (2 ^ i.val).testBit j.val := by
    rw [Nat.testBit_xor] at hz
    cases h₁ : ((Coordinates.conjugateRows.get 0).get i).testBit j.val <;>
      cases h₂ : (2 ^ i.val).testBit j.val <;> simp_all
  rw [← decode_packedOne]
  simp only [decodeRows, packedOne, get_ofFn, hb]

private theorem seed_mem_flagDiagonalKernel : seed ∈ flagDiagonalHom.ker := by
  change flagDiagonalHom seed = 1
  ext i j
  rw [flagDiagonalHom_apply]
  have hs : coordinates seed = decodeRows (Coordinates.conjugateRows.get 0) :=
    seedConjugate_coordinates 0
  rw [hs]
  by_cases hij : flagBlock i = flagBlock j
  · rw [if_pos hij]
    exact seed_diagonal i j hij
  · rw [if_neg hij, Matrix.one_apply_ne (fun h => hij (congrArg flagBlock h))]

/-- The relative normal closure lies in the kernel of the diagonal-block action. -/
theorem seedNormalClosure_le_flagDiagonalKernel : seedNormalClosure ≤ flagDiagonalHom.ker := by
  apply Subgroup.normalClosure_le_normal
  intro g hg
  have : g = seed := Set.mem_singleton_iff.mp hg
  subst g
  exact seed_mem_flagDiagonalKernel

/-- The normal closure of the literal max4 seed is a two-group. -/
theorem seedNormalClosure_isPGroup : IsPGroup 2 seedNormalClosure :=
  flagDiagonalKernel_isPGroup.of_injective
    (Subgroup.inclusion seedNormalClosure_le_flagDiagonalKernel)
    (Subgroup.inclusion_injective _)

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo
