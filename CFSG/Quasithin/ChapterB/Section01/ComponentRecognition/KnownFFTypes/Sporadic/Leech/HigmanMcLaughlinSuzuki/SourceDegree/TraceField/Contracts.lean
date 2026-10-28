module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.Inputs

/-!
# The two HS inputs for the order-eleven trace argument

Taking the 512th power removes the two-part of the order of an HS element.
The odd-order classes other than the two classes of order eleven are conjugate
to their squares; the order-eleven classes are conjugate to their fourth powers.
The representation input is fixed-point-freeness of order-eleven elements on
every faithful absolutely irreducible degree-twenty module. These are contracts,
not assertions that either calculation has been established.

The sibling `TraceField` module proves that these two inputs imply the exact
`DegreeTwentyTraceField` contract. Neither a binary ground field nor a cubic
ratio is assumed. The group carrier is the actual published degree-100 action.

Source: Guralnick--Malle, *Classification of 2F-modules, I*, Proposition 5.1,
HS paragraph, p.16; ATLAS of Finite Group Representations, HSG1-p100B0 and
HSG1-f2r20B0. A calculation in that single module does not prove the universal
representation contract below.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField
universe v

/-- The actual HS power fusion needed by the trace calculation. -/
def PowerFusion : Prop :=
  ∀ g : KnownSimple.SporadicName.hs.Carrier,
    IsConj (g ^ 512) (g ^ 1024) ∨
      (orderOf (g ^ 512) = 11 ∧ IsConj (g ^ 512) (g ^ 2048))

/-- Fixed-point-freeness at order eleven in every absolute degree-twenty
representation of the actual carrier, with inherited simplicity. -/
def DegreeTwentyElevenFixedFree : Prop :=
  IsSimpleGroup KnownSimple.SporadicName.hs.Carrier →
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (W : Type v) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K KnownSimple.SporadicName.hs.Carrier W),
    Function.Injective τ → τ.IsAbsolutelyIrreducible →
      Module.finrank K W = 20 →
        ∀ g, orderOf g = 11 → LinearMap.ker (τ g - 1) = ⊥

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField
