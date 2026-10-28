module

public import Theory.GroupTheory.SimpleSectionTwoExponent
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent
public import Theory.SpecificGroups.Suzuki.SylowSquares
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.Models

/-!
# The marked rank-one quotients do not occur in binary SL₂ sections

Both original quotient families have a two-subgroup with a nonidentity square.
For PSU₃ this is the Hermitian root group; for Suzuki it is the actual Sylow
root group. The section exponent lemma excludes these quotients from any
solvable-kernel representation in binary SL₂. In particular this applies to
the literal residual maps through rank-two parabolic Levi quotients.

Source: Aschbacher--Smith 4.4.12, printed pp.621--622; the root calculations
are Huppert II.10 and Huppert--Blackburn III.XI.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

/-- The original unitary central quotient has a two-subgroup of exponent four. -/
theorem unitary_not_two_exponent {S : Type*} [Group S]
    {s : ℕ} (hs : 2 ≤ s) (hu : ClassicalGroup.IsPSU S 3 (2 ^ s)) :
    ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1 := by
  intro hS
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hu
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := s * 2) (by
    simpa only [Nat.card_eq_fintype_card,pow_mul] using hcard)
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s (by omega) hcard hconj
  obtain ⟨t⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2 ^ s) hcard hf
  let K := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let f := (e.trans t).symm.toMonoidHom.comp
    (BenderSuzuki.External.hermitianUnipotentPSU K rfl)
  have hi : Function.Injective f := (e.trans t).symm.injective.comp
    (HermitianForm.EvenInner.root_injective K rfl)
  have hp : IsPGroup 2 (BenderSuzuki.External.hermitianUnipotentCoord K) := by
    intro x
    refine ⟨2,?_⟩
    have hh : (x ^ 2) ^ 2 = 1 :=
      (HermitianForm.EvenSemilinear.square_eq_one_iff_first_zero K _).mpr (by
        rw [HermitianForm.EvenInner.square_coordinates])
    simpa only [← pow_mul,show 2 * 2 = 2 ^ 2 from rfl] using hh
  obtain ⟨x,hx⟩ := HermitianForm.EvenSemilinear.coord_first_surjective K hcard hf (1 : F)
  have hx2 : x ^ 2 = 1 := by
    apply hi
    simpa only [map_pow,map_one,Subgroup.coe_pow,Subgroup.coe_one,
      MonoidHom.coe_rangeRestrict] using congrArg Subtype.val
      (hS f.range (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
        (f.rangeRestrict x))
  exact one_ne_zero (hx.symm.trans
    ((HermitianForm.EvenSemilinear.square_eq_one_iff_first_zero K x).mp hx2))

/-- The same obstruction on the actual Suzuki carrier, with its given marking. -/
theorem suzuki_not_two_exponent {S : Type*} [Group S] [Finite S]
    {m : ℕ} (hm : 1 ≤ m) (e : S ≃* SuzukiMatrixGroup m) :
    ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1 := by
  intro hS
  let P : Sylow 2 S := Classical.choice inferInstance
  obtain ⟨x,hx⟩ := suzukiSylow_exists_nontrivial_square (by omega) e P
  exact hx (hS P P.isPGroup' x)

/-- Removing the actual representation's solvable kernel cannot hide the
nonidentity square in a nonsolvable simple quotient. -/
theorem no_rankOne_quotient_in_binary_linear_two
    {A S F : Type*} [Group A] [Group S] [Finite S] [IsSimpleGroup S]
    [Field F] [Finite F] [CharP F 2]
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : A →* S) (hπ : Function.Surjective π)
    (f : A →* SL(2,F)) [Group.IsSolvable f.ker] : False :=
  hexp (SimpleSection.two_exponent_of_solvable_representation hS
    Matrix.SpecialLinearGroup.twoSubgroup_pow_two f π hπ)

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
