module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup

/-!
# The symplectic-four upper E-generation calculation

The nonbinary intrinsic case is proved using the two actual determinant
kernels, their SL₂ quotients and the weak-closure normalizer. Perfectness
identifies the derived matrix carrier with the full matrix group only when
the field has more than two elements. Transport gives the corresponding
source case when the generalized Fitting subgroup is the whole group.
The native `Sp F` is definitionally the ATLAS carrier `Sp 2 F`: both are
`Matrix.symplecticGroup (Fin 2) F`. The legacy non-module ATLAS import is
therefore unnecessary.

The binary case and proper outer extensions, including actions that
interchange the parabolics, remain necessary for the full E.1.14(1) statement.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.14(1), printed p.214, citing Aschbacher (1982), Lemma 4.7.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- An actual nonbinary derived symplectic model has the source upper bound.
The exponent restriction preserves the binary derived-group exception. -/
theorem isEGenerated_of_nonbinary_model {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (e : G ≃* commutator (Sp F)) : IsEGenerated f G := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ f from Nat.pow_lt_pow_right (by decide) hf)
  exact (isEGenerated_sp_nonbinary hF hf).map_equiv
    (e.trans (derivedEquivFull_of_card_gt_two hq)).symm

/-- The nonbinary case of the source theorem with no proper outer extension.
Simplicity and SQTK are unnecessary in this subcase. -/
theorem isEGenerated_nonbinary_of_generalizedFitting_eq_top {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (e : generalizedFitting G ≃* commutator (Sp F))
    (hL : generalizedFitting G = ⊤) : IsEGenerated f G :=
  isEGenerated_of_nonbinary_model hF hf
    ((topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)).trans e)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour
