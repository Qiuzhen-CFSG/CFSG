module

public import Theory.SpecificGroups.ReeTwo.InvolutionCharacters
public import Theory.GroupTheory.CentricRadicalObstructions

/-!
# The exponent-two branch of the small Ree two character kernels

Both alternative characters restrict trivially to every subgroup of exponent
two, and more generally to every subgroup of the first omega subgroup of the
Sylow model. Their restricted kernels are therefore characteristic.

A small centric intrinsic radical candidate cannot have a two-group as its
full automorphism group, by the p-group normalizer condition. The remaining
exhaustion of small intrinsic radical candidates is not asserted here.

Source: van Beek (2024), Proposition 3.1, p. 10, motivates the candidate
analysis. The character calculation uses the verified Shinoda coordinate model
through `InvolutionCharacters`; no external computation is a proof input.
-/

namespace ReeTwo.SylowModel

/-- Subgroups of the first omega subgroup have trivial restricted alternative
characters. -/
public theorem alternativeCharacter_ker_eq_top_of_le_omega
    (χ : SylowModel →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter)
    (U : Subgroup SylowModel) (hU : U ≤ omega₁ SylowModel (p := 2)) :
    (χ.comp U.subtype).ker = ⊤ := by
  apply top_unique
  intro x _
  exact omega_le_alternativeCharacter_ker χ hχ (hU x.property)

/-- In particular, the alternative character kernels on subgroups of the
first omega subgroup are characteristic. -/
public theorem alternativeCharacter_ker_characteristic_of_le_omega
    (χ : SylowModel →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter)
    (U : Subgroup SylowModel) (hU : U ≤ omega₁ SylowModel (p := 2)) :
    (χ.comp U.subtype).ker.Characteristic := by
  rw [alternativeCharacter_ker_eq_top_of_le_omega χ hχ U hU]
  infer_instance

/-- Both alternative characters are trivial on any subgroup of exponent two. -/
public theorem alternativeCharacter_ker_eq_top_of_exponent_two
    (χ : SylowModel →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter)
    (U : Subgroup SylowModel) (hU : ∀ x : U, x ^ 2 = 1) :
    (χ.comp U.subtype).ker = ⊤ := by
  apply top_unique
  intro x _
  apply alternativeCharacter_eq_one_of_square_eq_one χ hχ
  exact congrArg Subtype.val (hU x)

/-- The characteristic-kernel conclusion for exponent-two candidates needs
neither centricity nor the intrinsic radical condition. -/
public theorem alternativeCharacter_ker_characteristic_of_exponent_two
    (χ : SylowModel →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter)
    (U : Subgroup SylowModel) (hU : ∀ x : U, x ^ 2 = 1) :
    (χ.comp U.subtype).ker.Characteristic := by
  rw [alternativeCharacter_ker_eq_top_of_exponent_two χ hχ U hU]
  infer_instance

/-- The full automorphism group of a small centric intrinsic radical candidate
is not a two-group. -/
public theorem not_isPGroup_mulAut_of_small_intrinsic_radical
    (U : Subgroup SylowModel)
    (hcent : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hcard : Nat.card U < 1024) : ¬ IsPGroup 2 (MulAut U) := by
  intro ha
  have htop := Subgroup.eq_top_of_intrinsic_radical_of_isPGroup_mulAut
    (IsPGroup.of_card (n := 12) card) U hcent hrad ha
  rw [htop, Subgroup.card_top, card] at hcard
  omega

end ReeTwo.SylowModel
