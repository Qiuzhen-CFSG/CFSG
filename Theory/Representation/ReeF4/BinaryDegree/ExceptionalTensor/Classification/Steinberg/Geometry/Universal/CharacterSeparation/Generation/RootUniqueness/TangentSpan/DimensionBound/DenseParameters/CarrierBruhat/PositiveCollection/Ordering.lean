module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat.Basic
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.Coordinates

/-!
# An actual ordering of the 24 positive F4 roots

Negation pairs the positive and negative roots. The concrete 48-root
coordinate equivalence therefore gives 24 positive roots and an enumeration.
Source: the F4 realization of GLS3 1.8, `refs/KGroup/GLS3/Chapter1.tex`.
-/

@[expose] public section
noncomputable section
namespace Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat
open StandardRootSystem
local instance positiveOrderingRootNeg : InvolutiveNeg Root := typeF4RootPairing.indexNeg

/-- Exactly half of the 48 concrete F4 roots are positive. -/
theorem positiveRoot_card : Nat.card PositiveRoot = 24 := by
  classical
  let e : PositiveRoot ≃ {r : Root // ¬ typeF4RootPairing_base.IsPos r} :=
    { toFun := fun r => ⟨-r.val, by
        rw [RootPairing.Base.IsPos.neg_iff_not]
        exact not_not.mpr r.property⟩
      invFun := fun r => ⟨-r.val,
        (RootPairing.Base.IsPos.neg_iff_not _ _).mpr r.property⟩
      left_inv := fun r => Subtype.ext (neg_neg r.val)
      right_inv := fun r => Subtype.ext (neg_neg r.val) }
  have he := Nat.card_congr e
  have ht : Nat.card Root = 48 := by
    simpa using (Nat.card_congr
      ReeF4.Cartan.FieldSeparation.TraceValues.rootEquiv).symm
  have hs := Nat.card_congr (Equiv.sumCompl typeF4RootPairing_base.IsPos)
  rw [Nat.card_sum, ht, ← he] at hs
  change Nat.card PositiveRoot + Nat.card PositiveRoot = 48 at hs
  omega

/-- A genuine enumeration of the 24 positive roots. -/
def positiveOrdering : PositiveOrdering := by
  classical
  letI : Fintype PositiveRoot := Fintype.ofFinite _
  exact (Fintype.equivFinOfCardEq (by
    simpa only [Fintype.card_eq_nat_card] using positiveRoot_card)).symm

end Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat
