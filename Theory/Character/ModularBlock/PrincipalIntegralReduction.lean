module

public import Theory.Character.ModularBlock.Cartan
public import Theory.Character.ModularBlock.BrauerIntegralReduction

/-!
# Principal-block membership after integral reduction

An integral matrix representation over the localization at the prescribed
cyclotomic prime can be mapped both to the complex numbers and to the splitting
residue field. If its complex character is an ordinary character in the
principal congruence block, its reduction is in the principal modular block.

The ordinary principal selector acts identically on the complex model.
Injectivity of the localization embedding detects this identity integrally;
coefficient reduction then preserves it. The reduced selector is exactly the
one used by `Cartan.InPrincipalBlock`. This proves the block-membership part of
ordinary lattice reduction. The companion `BrauerIntegralReduction` supplies
the Brauer eigenvalue comparison; neither result assumes existence of integral
models. See Serre, *Linear Representations of Finite Groups*, Chapter 15,
and the selector construction in
`PrincipalSelector.lean`.
-/

public section

noncomputable section
namespace ModularBlock.Cartan
open PrincipalBlockConstruction BrauerCoefficientExtension
variable {G : Type*} [Group G] [Finite G]
variable (d : PrincipalCongruenceBlockData G)

theorem splittingSelector_eq_map_localized :
    splittingSelector d = MonoidAlgebra.mapRingHom G (localizedReduction d)
      (BlockOrthogonality.localizedPrincipalBlockElement d) := by
  ext g
  rfl

/-- Reduction of an integral model of an ordinary block character lies in the
principal block of the actual splitting residue field. -/
theorem inPrincipalBlock_mapCoefficients {m : ℕ}
    (σ : Representation (Localization.AtPrime d.primeIdeal) G
      (Fin m → Localization.AtPrime d.primeIdeal))
    (i : d.I) (hi : i ∈ d.block)
    (hχ : d.chi i = characterClassFunction
      (Representation.mapCoefficients (BlockOrthogonality.localizationToComplex d.primeIdeal) σ)) :
    InPrincipalBlock d (Representation.mapCoefficients (localizedReduction d) σ) := by
  have hcomplex := BlockOrthogonality.principalBlockElement_action d i
    (Representation.mapCoefficients (BlockOrthogonality.localizationToComplex d.primeIdeal) σ) hχ
  rw [if_pos hi, one_smul] at hcomplex
  have hintegral := Representation.asAlgebraHom_eq_one_of_mapCoefficients
    (BlockOrthogonality.localizationToComplex d.primeIdeal)
    (BlockOrthogonality.localizationToComplex_injective d) σ
    (BlockOrthogonality.localizedPrincipalBlockElement d) hcomplex
  rw [InPrincipalBlock, splittingSelector_eq_map_localized]
  exact Representation.mapCoefficients_asAlgebraHom_eq_one (localizedReduction d) σ _ hintegral

end ModularBlock.Cartan
