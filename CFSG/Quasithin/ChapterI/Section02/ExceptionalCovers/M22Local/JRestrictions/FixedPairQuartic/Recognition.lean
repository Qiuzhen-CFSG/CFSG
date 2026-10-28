module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions.FixedPairQuartic
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions.FixedPairBinary
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix

/-!
# Compatible quartic hexad recognition for the fixed-pair calculation

The data retain the actual hexad preimage, radical and six-point quotient.
A section of this quotient gives an actual A₆ complement by
`hexadSection_isComplement`. Its action on the radical is identified with the
intrinsic signed action, explicitly precomposed by the pentad automorphism.
The center comparison is with the actual ambient center and the proved C₄
center of the intrinsic model.

This is the permitted earlier-source recognition input for Aschbacher–Smith
I.2.2(6a), printed pp.410 and 412. The quartic-hexad source assembly must
construct it; neither requested fixed-pair conclusion is assumed here.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
open BinaryPermutation GLS3.Chapter5
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
variable {K : Type*} [Group K]
/-- An actual hexad complement and radical coordinates for the intrinsic signed action.
The six-point quotient is native, and its action has the explicit pentad marking.
No pair-core isomorphism or residual placement is part of this input. -/
structure Recognition (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) where
  sectionMap : alternatingGroup (Fin 6) →* hexadPreimage e B
  section_eq : ∀ a, hexadSixMap e hB (sectionMap a) = a
  coordinates : hexadRadical e B ≃* EvenCliffordSix.Model
  equivariant : ∀ a r, coordinates (hexadConjugation e B (sectionMap a) r) =
    EvenCliffordSix.precomposedAction outerAltAut a (coordinates r)
  center_eq : ∀ r, r.val ∈ center K ↔ coordinates r ∈ center EvenCliffordSix.Model


end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
