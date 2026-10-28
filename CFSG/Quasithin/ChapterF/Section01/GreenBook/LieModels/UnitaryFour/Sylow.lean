module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourFieldCoordinates
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointStructure

/-!
# The explicit Sylow subgroup in the unitary-four flag amalgam

In the stored GF(2^(2n)) model, the upper-unitriangular SU₄ subgroup has
order (2^n)^6. Its faithful image under the canonical projective map is a
Sylow two-subgroup contained in both flag stabilizers and in the first local
factor. The matrix and projective ambient orders have two-adic valuation 6n;
the remaining factor is the odd index of this explicit subgroup.

The generic proof counts the Heisenberg kernel and its middle-block image,
and proves maximality by fixed vectors. Here the finite-field cardinalities
identify the count with q^6. The final theorem discharges the actual Sylow
placement assumption of `PointLocal.source_II_point`.

Source: Aschbacher--Smith F.1.6 and F.1.12(I)(6), (II)(i), printed
pp.261, 263--264 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
variable (n : ℕ) (hn : 1 ≤ n)

instance projectiveGroup_finite : Finite (ProjectiveGroup n hn) :=
  Finite.of_surjective (projection n hn)
    (UnitaryFourFlag.project_surjective (MatrixField n) (standardForm n hn))

def upperMatrix : Subgroup (MatrixGroup n hn) :=
  UnitaryFourSylow.upper (MatrixField n) (fieldConj n) (fieldConj_involutive n hn)

theorem mem_upperMatrix (a : MatrixGroup n hn) : a ∈ upperMatrix n hn ↔
    (∀ i j : Fin 4, j < i → a.val.val i j = 0) ∧ ∀ i, a.val.val i i = 1 :=
  UnitaryFourSylow.mem_upper_iff_entries _ _ _ a

theorem upperMatrix_card : Nat.card (upperMatrix n hn) = (2 ^ n) ^ 6 := by
  refine (UnitaryFourSylow.upper_card (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn)).trans ?_
  rw [matrixField_card n hn]
  change ((2 ^ n) ^ 2) ^ 2 * Nat.card (PointLocal.FixedField n) ^ 2 = _
  rw [PointLocal.fixedField_card n hn]
  ring

def matrixSylow : Sylow 2 (MatrixGroup n hn) :=
  UnitaryFourSylow.sylow (MatrixField n) (fieldConj n) (fieldConj_involutive n hn)

@[simp] theorem coe_matrixSylow : (matrixSylow n hn : Subgroup _) = upperMatrix n hn := rfl

theorem matrixSylow_card : Nat.card (matrixSylow n hn) = (2 ^ n) ^ 6 :=
  upperMatrix_card n hn

theorem upperMatrix_le_pointLocal : upperMatrix n hn ≤ PointLocal.MatrixLocal n hn := by
  intro a ha
  exact ((UnitaryFourSylow.mem_upper _ _ _ a).mp ha).1

theorem upperMatrix_le_overlap : upperMatrix n hn ≤ overlapMatrix n hn :=
  UnitaryFourSylow.upper_le_borel _ _ _

def upperProjective : Subgroup (ProjectiveGroup n hn) :=
  (upperMatrix n hn).map (projection n hn)

/-- The actual projective quotient map restricts to an isomorphism on the subgroup. -/
def upperProjectEquiv : upperMatrix n hn ≃* upperProjective n hn :=
  UnitaryFourSylow.upperProjectEquiv (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn)

@[simp] theorem upperProjectEquiv_apply (a : upperMatrix n hn) :
    (upperProjectEquiv n hn a).val = projection n hn a.val := rfl

theorem upperProjection_injective :
    Function.Injective ((projection n hn).comp (upperMatrix n hn).subtype) :=
  (projection_injective n hn).comp Subtype.val_injective

theorem upperProjective_card : Nat.card (upperProjective n hn) = (2 ^ n) ^ 6 :=
  (Nat.card_congr (upperProjectEquiv n hn).symm.toEquiv).trans (upperMatrix_card n hn)

def projectiveSylow : Sylow 2 (ProjectiveGroup n hn) :=
  UnitaryFourSylow.projectiveSylow (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn)

@[simp] theorem coe_projectiveSylow :
    (projectiveSylow n hn : Subgroup _) = upperProjective n hn := rfl

theorem projectiveSylow_card : Nat.card (projectiveSylow n hn) = (2 ^ n) ^ 6 :=
  upperProjective_card n hn

theorem upperProjective_le_overlap : upperProjective n hn ≤ overlap n hn :=
  Subgroup.map_mono (upperMatrix_le_overlap n hn)

theorem upperProjective_le_pointLocal :
    upperProjective n hn ≤ PointLocal.ProjectiveLocal n hn :=
  Subgroup.map_mono (upperMatrix_le_pointLocal n hn)

theorem matrix_order_twoPart :
    2 ^ (Nat.card (MatrixGroup n hn)).factorization 2 = (2 ^ n) ^ 6 :=
  (matrixSylow n hn).card_eq_multiplicity.symm.trans (matrixSylow_card n hn)

theorem projective_order_twoPart :
    2 ^ (Nat.card (ProjectiveGroup n hn)).factorization 2 = (2 ^ n) ^ 6 :=
  (projectiveSylow n hn).card_eq_multiplicity.symm.trans (projectiveSylow_card n hn)

theorem matrix_order_twoValuation :
    (Nat.card (MatrixGroup n hn)).factorization 2 = n * 6 :=
  Nat.pow_right_injective (by decide : 1 < 2)
    ((matrix_order_twoPart n hn).trans (pow_mul 2 n 6).symm)

theorem projective_order_twoValuation :
    (Nat.card (ProjectiveGroup n hn)).factorization 2 = n * 6 :=
  Nat.pow_right_injective (by decide : 1 < 2)
    ((projective_order_twoPart n hn).trans (pow_mul 2 n 6).symm)

theorem upperMatrix_index_odd : Odd (upperMatrix n hn).index := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact (matrixSylow n hn).not_dvd_index

theorem upperProjective_index_odd : Odd (upperProjective n hn).index := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact (projectiveSylow n hn).not_dvd_index

theorem matrix_order_eq :
    Nat.card (MatrixGroup n hn) = (2 ^ n) ^ 6 * (upperMatrix n hn).index := by
  rw [← upperMatrix_card n hn]
  exact (upperMatrix n hn).card_mul_index.symm

theorem projective_order_eq :
    Nat.card (ProjectiveGroup n hn) = (2 ^ n) ^ 6 * (upperProjective n hn).index := by
  rw [← upperProjective_card n hn]
  exact (upperProjective n hn).card_mul_index.symm

/-- The chosen Sylow simultaneously lies in both literal flag stabilizers. -/
theorem projectiveSylow_le_parabolics :
    (projectiveSylow n hn : Subgroup _) ≤ pointParabolic n hn ∧
    (projectiveSylow n hn : Subgroup _) ≤ planeParabolic n hn := by
  rw [← le_inf_iff, exact_overlap]
  exact upperProjective_le_overlap n hn

/-- The explicit Sylow discharges the placement assumption in the first-factor
application of F.1.12(II)(i). -/
theorem point_source_II_with_standardSylow (hn2 : 1 < n) :
    Subgroup.solvableResidual (PointLocal.ProjectiveLocal n hn) = ⊤ ∧
    (projectiveSylow n hn : Subgroup (ProjectiveGroup n hn)) ≤ PointLocal.ProjectiveLocal n hn ∧
    (pCore 2 (PointLocal.ProjectiveLocal n hn ⊔
        (projectiveSylow n hn : Subgroup (ProjectiveGroup n hn)) :
        Subgroup (ProjectiveGroup n hn))).map
        (PointLocal.ProjectiveLocal n hn ⊔
          (projectiveSylow n hn : Subgroup (ProjectiveGroup n hn))).subtype =
      (pCore 2 (PointLocal.ProjectiveLocal n hn)).map
        (PointLocal.ProjectiveLocal n hn).subtype :=
  PointLocal.source_II_point n hn hn2 (projectiveSylow n hn)
    (projectiveSylow_le_parabolics n hn).1

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
