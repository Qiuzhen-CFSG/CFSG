module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.QuotientClassification
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.CompleteCover

/-!
# Native J₄ large-center radical quotients and normal residual exclusions

The completed elementary-normalizer cover supplies every geometric premise.
An arbitrary nontrivial two-radical with center of order at least 64 has the
full normalizer quotient SL₅(2), M₂₄ or A₈, and its intrinsic normalizer core
is exactly the original radical restricted to that normalizer. Whole-normal
residuals with U₃(3) or SL₃(2) full-core quotients are therefore impossible.

This final source assembly resides above Theory because the completed native
cover currently uses the CFSG-layer pure-first line calculation. No source
configuration or classification hypothesis occurs in the native theorem.
The original Chapter12 and Chapter13 configurations consume these results.
Source: Kleidman--Wilson (1988), §2; An--O'Brien--Wilson (2003), §4 and Table1.
-/
public section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals

/-- Full intrinsic quotient classification for every native large-center radical. -/
theorem radical_quotient (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (center P)) :
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      Sporadic.Mathieu.M24) ∨
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      alternatingGroup (Fin 8)) :=
  radical_quotient_of_cover PureFirstNormalizers.CompleteCover.maximalTwoLocalCover P hP hlarge

/-- The denominator is the full normalizer two-core, with the literal original
radical inclusion, together with the selective quotient classification. -/
theorem radical_normalizer_structure (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (center P)) :
    pCore 2 (normalizer (P : Set Model)) = P.subgroupOf (normalizer (P : Set Model)) ∧
    (Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      Sporadic.Mathieu.M24) ∨
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      alternatingGroup (Fin 8))) :=
  ⟨radical_core_eq P hP,radical_quotient P hP hlarge⟩

/-- The entire normalizer has no whole-normal residual with the actual U₃(3) quotient. -/
theorem unitary_radical_false (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (center P))
    (B : Subgroup (normalizer (P : Set Model))) [B.Normal]
    (b : (B ⧸ pCore 2 B) ≃* commutator (Atlas.G2.Model (ZMod 2))) : False :=
  unitary_normal_residual_quotients_excluded B b (radical_quotient P hP hlarge)

/-- The analogous whole-normal SL₃(2) residual is excluded without local maximality. -/
theorem binaryThree_radical_false (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (center P))
    (B : Subgroup (normalizer (P : Set Model))) [B.Normal]
    (b : (B ⧸ pCore 2 B) ≃* BinaryLinearThree.Group) : False :=
  binaryThree_normal_residual_quotients_excluded B b (radical_quotient P hP hlarge)

end Janko4.LocalStructure.LargeCenterRadicals
