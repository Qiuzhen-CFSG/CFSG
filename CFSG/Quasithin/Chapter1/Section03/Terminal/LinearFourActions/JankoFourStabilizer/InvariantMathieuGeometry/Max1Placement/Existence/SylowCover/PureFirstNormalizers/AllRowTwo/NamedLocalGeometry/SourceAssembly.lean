module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.RowNormalizer
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.AmbientApplication

/-!
# The complete all-row-two pure-first source branch

The exact ambient census supplies one conjugator identifying the original
subgroup with a literal row. The line row has the full max4 normalizer; for
every nonline row the canonical intersection of all ambient F occurrences
contains a certified second-class element. The whole-normalizer theorem then
places the original maximal two-local in a literal named local. All finite
incidence, mixedness and row-identification premises are discharged.

The radical application uses the original subgroup and normalizer inclusions.
Its relative normalizer and two-core are transported by the actual inclusion
map, retaining the original radical rather than a replacement conjugate.
This is the no-native-pair branch; the complementary native-pair-contained
branch and the remaining classification assembly belong to their owners.
Source: Kleidman--Wilson (1988), Corollary 1.2.2(a), Section 2.1 and
Proposition 2.2.3, pp.488--491.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
open FiniteConfigurations LargeCenterRadicals
open ElementaryNormalizerCover.PureTwoA.NativePair
attribute [local irreducible] modelGroup matrixA matrixB

/-- The original maximal-two-local endpoint for a pure-first elementary subgroup
of order greater than four containing no conjugate of the native row-seven pair.
There are no row-census, incidence, container or normalizer-placement premises. -/
theorem all_row_two_nativeLocalPlacement (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hcard : 4 < Nat.card X)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hnoPair : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    NativeLocalPlacement (normalizer (X : Set Model)) := by
  obtain ⟨g,i,hX,_,_,_⟩ := conjugate_row_classification X hcard hpure hnoPair
  exact conjugate_row_nativeLocalPlacement X g i hX hmax

/-- Actual arbitrary-radical application of the completed source branch. The
whole original normalizer lies in a named two-local, the restricted subgroup
is still radical, and both relative normalizer and two-core map back literally. -/
theorem radical_local_of_all_row_two (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hcard : 4 < Nat.card X)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hnoPair : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (hPX : normalizer (P : Set Model) ≤ normalizer (X : Set Model))
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ H : Subgroup Model, IsTwoLocal H ∧ NativeLocalPlacement H ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  obtain ⟨g,i,hX,_,_,_⟩ := conjugate_row_classification X hcard hpure hnoPair
  exact radical_local_of_conjugate_row P X hP hPX hmax g i hX

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry

