module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
public import Theory.GroupTheory.Amalgam.RankTwoTransport

/-!
# The concrete unitary-four flag amalgam

Matrices are over GF(2^(2n)), with Hermitian involution x ↦ x^(2^n).
The two isotropic flag stabilizers and their whole intersection define the
matrix amalgam. The same injective projection to the actual projective special
unitary group transports all three groups, so the maps agree on the overlap.

This supplies the flag construction for Aschbacher--Smith F.1.12(I)(6), printed
pp. 263--264. The Sylow calculation, the distinct local factors Lᵢ inside the
parabolics, their radicals and quotient actions, and the degree-two extension
remain separate obligations. In particular the full overlap is not asserted
to be a Sylow subgroup, and the full parabolics are not used as Lᵢ.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour

open BenderSuzuki.MatrixGroups Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag

/-- Matrix field; the unitary parameter is `2^n`, not its square. -/
abbrev MatrixField (n : ℕ) := GaloisField 2 (n * 2)

theorem matrixField_card (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (MatrixField n) = (2 ^ n) ^ 2 := by
  rw [GaloisField.card 2 (n * 2) (by omega), pow_mul]

/-- The Hermitian field automorphism, halfway around the Galois group. -/
def fieldConj (n : ℕ) : MatrixField n ≃+* MatrixField n :=
  iterateFrobeniusEquiv (MatrixField n) 2 n

theorem fieldConj_apply (n : ℕ) (x : MatrixField n) :
    fieldConj n x = x ^ (2 ^ n) := rfl

theorem fieldConj_involutive (n : ℕ) (hn : 1 ≤ n) :
    Function.Involutive (fieldConj n) := by
  intro x
  rw [fieldConj_apply, fieldConj_apply, ← pow_mul, ← pow_two,
    ← matrixField_card n hn]
  let := Fintype.ofFinite (MatrixField n)
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

/-- The split Hermitian form of Witt index two in dimension four. -/
def standardForm (n : ℕ) (hn : 1 ≤ n) : HermitianForm 4 (MatrixField n) :=
  form (MatrixField n) (fieldConj n) (fieldConj_involutive n hn)

variable (n : ℕ) (hn : 1 ≤ n)

abbrev MatrixGroup := SU (MatrixField n) (standardForm n hn)
abbrev ProjectiveGroup := PSU (MatrixField n) (standardForm n hn)

/-- The actual canonical projective map. -/
def projection : MatrixGroup n hn →* ProjectiveGroup n hn :=
  project (MatrixField n) (standardForm n hn)

theorem projection_injective : Function.Injective (projection n hn) :=
  project_injective (MatrixField n) (standardForm n hn)

def pointParabolicMatrix : Subgroup (MatrixGroup n hn) :=
  pointParabolicSU (MatrixField n) (standardForm n hn)

def planeParabolicMatrix : Subgroup (MatrixGroup n hn) :=
  planeParabolicSU (MatrixField n) (standardForm n hn)

def overlapMatrix : Subgroup (MatrixGroup n hn) :=
  pointParabolicMatrix n hn ⊓ planeParabolicMatrix n hn

def pointParabolic : Subgroup (ProjectiveGroup n hn) :=
  (pointParabolicMatrix n hn).map (projection n hn)

def planeParabolic : Subgroup (ProjectiveGroup n hn) :=
  (planeParabolicMatrix n hn).map (projection n hn)

def overlap : Subgroup (ProjectiveGroup n hn) :=
  (overlapMatrix n hn).map (projection n hn)

theorem parabolics_ne : pointParabolic n hn ≠ planeParabolic n hn := by
  intro h
  have hm := Subgroup.map_injective (projection_injective n hn) h
  exact parabolicsSU_ne (MatrixField n) (fieldConj n) (fieldConj_involutive n hn) hm

/-- The projective overlap is the image of the whole matrix flag stabilizer. -/
theorem exact_overlap : pointParabolic n hn ⊓ planeParabolic n hn = overlap n hn :=
  (Subgroup.map_inf _ _ (projection n hn) (projection_injective n hn)).symm

def matrixAmalgam : RankTwoAmalgam
    (pointParabolicMatrix n hn) (overlapMatrix n hn) (planeParabolicMatrix n hn) :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

def amalgam : RankTwoAmalgam
    (pointParabolic n hn) (overlap n hn) (planeParabolic n hn) :=
  RankTwoAmalgam.ofSubgroups _ _ _
    (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)

/-- All three isomorphisms are restrictions of the same projective map. -/
def projectIso : RankTwoAmalgam.Iso (matrixAmalgam n hn) (amalgam n hn) :=
  RankTwoAmalgam.ofSubgroupsMapIso (projection n hn) (projection_injective n hn)
    _ _ _ inf_le_left inf_le_right

theorem left_injective : Function.Injective (amalgam n hn).left :=
  RankTwoAmalgam.ofSubgroups_left_injective _ _ _ _ _

theorem right_injective : Function.Injective (amalgam n hn).right :=
  RankTwoAmalgam.ofSubgroups_right_injective _ _ _ _ _

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
