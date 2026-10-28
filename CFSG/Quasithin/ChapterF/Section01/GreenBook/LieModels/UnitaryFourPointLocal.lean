module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
public import Theory.FieldTheory.QuadraticFrobeniusFixed
public import Theory.PGroupCore

/-!
# The first unitary-four local factor over GF(q²)

We specialize the vector stabilizer and its middle-block kernel to the stored
quadratic Frobenius model. The fixed field is the actual fixed subfield of
that involution and has order q = 2^n. Thus the kernel has order q^5 and is a
normal two-subgroup of the local factor. This proves its inclusion in O₂;
equality, special structure and quotient/residual identification are separate
obligations in Aschbacher--Smith F.1.12(I)(6) and (II), printed pp. 263--264.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal

open Theory.SpecificGroups.ClassicalUnitary

variable (n : ℕ) (hn : 1 ≤ n)

abbrev FixedField := FixedBy.subfield (MatrixField n) (fieldConj n)

include hn in
theorem fixedField_card : Nat.card (FixedField n) = 2 ^ n := by
  change Nat.card (FixedBy.subfield (GaloisField 2 (n * 2))
    (iterateFrobeniusEquiv (GaloisField 2 (n * 2)) 2 n)) = 2 ^ n
  rw [Nat.mul_comm n 2]
  exact GaloisField.card_fixedBy_quadraticFrobenius 2 n (by omega)

/-- The local factor fixes e₀, not just its line. -/
abbrev MatrixLocal := UnitaryFourPointLocal.localSU (MatrixField n) (standardForm n hn)

abbrev ProjectiveLocal := UnitaryFourPointLocal.localPSU (MatrixField n) (standardForm n hn)

theorem matrixLocal_le_pointParabolic : MatrixLocal n hn ≤ pointParabolicMatrix n hn :=
  UnitaryFourPointLocal.localSU_le_pointParabolicSU _ _

instance matrixLocal_normal :
    ((MatrixLocal n hn).subgroupOf (pointParabolicMatrix n hn)).Normal :=
  UnitaryFourPointLocal.localSU_normal _ _

theorem projectiveLocal_le_pointParabolic : ProjectiveLocal n hn ≤ pointParabolic n hn :=
  UnitaryFourPointLocal.localPSU_le_pointParabolicPSU _ _

instance projectiveLocal_normal :
    ((ProjectiveLocal n hn).subgroupOf (pointParabolic n hn)).Normal :=
  UnitaryFourPointLocal.localPSU_normal _ _

def localEquiv : MatrixLocal n hn ≃* ProjectiveLocal n hn :=
  UnitaryFourPointLocal.localProjectEquiv _ _

@[simp] theorem localEquiv_apply (a : MatrixLocal n hn) :
    (localEquiv n hn a).val = projection n hn a.val := rfl

/-- The actual kernel of the action on the perpendicular quotient. -/
abbrev Radical : Subgroup (MatrixLocal n hn) :=
  UnitaryFourPointLocal.radical (MatrixField n) (fieldConj n) (fieldConj_involutive n hn)

instance radical_normal : (Radical n hn).Normal :=
  UnitaryFourPointLocal.radical_normal _ _ _

theorem radical_card : Nat.card (Radical n hn) = (2 ^ n) ^ 5 := by
  change Nat.card (UnitaryFourPointLocal.radical (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn)) = _
  rw [UnitaryFourPointLocal.radical_card, matrixField_card n hn]
  change (2 ^ n) ^ 2 * (2 ^ n) ^ 2 * Nat.card (FixedField n) = _
  rw [fixedField_card n hn]
  ring

theorem radical_isTwoGroup : IsPGroup 2 (Radical n hn) :=
  IsPGroup.of_card (n := n * 5) (by rw [radical_card, pow_mul])

/-- This is only one inclusion; the converse needs the quotient calculation. -/
theorem radical_le_twoCore : Radical n hn ≤ pCore 2 (MatrixLocal n hn) :=
  le_sSup ⟨inferInstance, radical_isTwoGroup n hn⟩

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal
