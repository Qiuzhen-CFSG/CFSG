module
public import Theory.GroupTheory.DihedralCentralProductFourSix.Factors
public import Theory.GroupTheory.DihedralCentralProductFourSix.Marked

/-!
# Intrinsic recognition of the fourfold and sixfold dihedral central products

An extraspecial two-group of order `2^(1+2e)` containing an elementary subgroup
of order `2^(e+1)` which contains its center is the central product of `e`
copies of D₈. Successive dihedral splittings construct all the factors; the
extraspecial elementary bound forces maximality at each stage. Multiplication
of the factors then identifies the group with the literal central-product
quotient. The fourfold and sixfold applications leave no factor or basis data
as hypotheses, and the sixfold target is the existing concrete model.

Source: Aschbacher–Smith, §8.2, Lemma 8.2.12(1), printed p.722 (PDF p.739).
-/

namespace DihedralCentralProductFourSix
open Subgroup

/-- Intrinsic recognition with `n + 1` dihedral factors. -/
public noncomputable def recognition (n : ℕ)
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hP : Nat.card P = 2 ^ (1 + 2 * (n + 1)))
    (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2 ^ (n + 2)) (hZA : center P ≤ A) : P ≃* Model n :=
  Classical.choice (by
    obtain ⟨f, _, hc, hz, hg⟩ := exists_dihedral_factor_maps n hP A hA hZA
    exact ⟨(markedRecognition f hc hz hg hP).symm⟩)

/-- The concrete quotient of `Fin 4 → DihedralGroup 4` by its three central
identifications. -/
public abbrev FourModel := Model 3

/-- An elementary subgroup of order 32 recognizes the fourfold plus type. -/
public noncomputable def fourRecognition
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hP : Nat.card P = 2 ^ (1 + 2 * 4))
    (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2 ^ (4 + 1)) (hZA : center P ≤ A) : P ≃* FourModel :=
  recognition 3 hP A hA hZA

/-- An elementary subgroup of order 128 recognizes the existing sixfold
quotient, with no hyperbolic-basis or generation assumption. -/
public noncomputable def sixRecognition
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hP : Nat.card P = 2 ^ (1 + 2 * 6))
    (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2 ^ (6 + 1)) (hZA : center P ≤ A) :
    P ≃* DihedralCentralProductSix.Model :=
  (recognition 5 hP A hA hZA).trans sixModelEquiv

end DihedralCentralProductFourSix
