module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallCentricParityContainment
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCentricCoreContainment
public import Theory.SpecificGroups.ReeTwo.SylowOmega

/-!
# Small centric intrinsic radical subgroups of the Ree two Sylow model

Every centric intrinsic radical subgroup of order less than 1024 lies in the
first omega subgroup. The verified parity census first puts the subgroup in
the parity character kernel. The even census then puts it in the core-character
kernel. Their intersection is exactly the first omega subgroup.

Source: the verified Shinoda (1975), (2.3), pp. 81–82, coordinate model and the
complete Lean censuses in `SmallCentricParityContainment` and
`SmallEvenCentricCoreContainment`. Van Beek (2024), Proposition 3.1, motivates
the local analysis; no external computational classification is assumed.
-/

namespace ReeTwo.SylowModel

/-- Every small centric intrinsic radical subgroup of the verified Ree two
Sylow model is contained in its first omega subgroup. -/
public theorem small_le_omega_of_intrinsic_radical
    (U : Subgroup SylowModel)
    (hcent : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hcard : Nat.card U < 1024) : U ≤ omega₁ SylowModel (p := 2) := by
  have hpar := small_le_character_ker_of_intrinsic_radical U hcent hrad hcard
  exact (le_omega_iff U).mpr
    ⟨hpar, smallEven_le_coreCharacter_ker U hcent hrad hcard hpar⟩

/-- The two verified alternative characters have characteristic restricted
kernels on every small centric intrinsic radical subgroup. -/
public theorem alternativeCharacter_ker_characteristic_of_small_intrinsic_radical
    (χ : SylowModel →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter)
    (U : Subgroup SylowModel)
    (hcent : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hcard : Nat.card U < 1024) :
    (χ.comp U.subtype).ker.Characteristic := by
  exact alternativeCharacter_ker_characteristic_of_le_omega χ hχ U
    (small_le_omega_of_intrinsic_radical U hcent hrad hcard)

end ReeTwo.SylowModel
