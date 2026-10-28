module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.Ordinary
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuBranch
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model

/-!
# Larger pure-first normalizers through a characteristic four-subgroup

For a pure first-class elementary subgroup of order greater than four, the
Section 2.1 plane route supplies a proper pure four-subgroup whose full
normalizer contains the original normalizer.  Once that route has positioned
the four-subgroup, endpoint containment upgrades by maximality to equality.
This module records that reusable upgrade while retaining all four literal
native endpoints: the source max2, the full F-normalizer, max1, and max4.

The characteristic plane and the max4 two-local input are deliberately
explicit.  Their producers are the source line/plane geometry and the native
max4 calculation; this leaf does not replace those geometric obligations.
Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA
open ElementaryNormalizerCover
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LinearFive
open SymmetricLinear
attribute [local irreducible] modelGroup matrixA matrixB SymmetricLinear.max4Subgroup

private theorem fullNormalizer_isTwoLocal : IsTwoLocal LinearFive.fullNormalizer := by
  rw [← LinearFive.M_F_eq_fullNormalizer]
  exact nativeF_generated_isTwoLocal

private theorem endpoint_eq_of_le
    (X L : Subgroup Model) (g : Model)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model)))
    (hL : IsTwoLocal L)
    (hN : normalizer (X : Set Model) ≤ L.map (MulAut.conj g).toMonoidHom) :
    normalizer (X : Set Model) = L.map (MulAut.conj g).toMonoidHom :=
  hmax.eq_of_le (hL.map_equiv (MulAut.conj g)) hN

private theorem larger_four_lt
    (X Y : Subgroup Model) (hY : Y ≤ X)
    (hcardX : 4 < Nat.card X) (hcardY : Nat.card Y = 4) : Y < X := by
  refine lt_of_le_of_ne hY ?_
  intro hEq
  have : Nat.card X = 4 := by rw [← hEq, hcardY]
  omega

/-- A proper normalized pure four-subgroup determines the whole larger endpoint.

The endpoint disjunction is literal, and the same ambient conjugator is kept
through the maximality upgrade.  The optional `hpure` argument is the source
pure-first hypothesis; the endpoint proof only needs its geometric consumer,
but retaining it keeps this theorem directly applicable to `hpure` in the
global cover assembly.
-/
theorem larger_pure_normalizer_of_four
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcardX : 4 < Nat.card X)
    (_hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model)))
    (Y : Subgroup Model) [IsElementaryAbelian 2 Y]
    (hYcard : Nat.card Y = 4) (hYX : Y ≤ X)
    (hYN : normalizer (X : Set Model) ≤ normalizer (Y : Set Model))
    (hendpoint :
      (∃ g : Model,
        normalizer (Y : Set Model) ≤
          sourceSubgroup.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g : Model,
        normalizer (Y : Set Model) ≤
          LinearFive.fullNormalizer.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g : Model,
        normalizer (Y : Set Model) ≤
          max1.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g : Model,
        normalizer (Y : Set Model) ≤
          SymmetricLinear.max4Subgroup.map (MulAut.conj g).toMonoidHom))
    (hmax4 : IsTwoLocal SymmetricLinear.max4Subgroup) :
    Y < X ∧
      ((∃ g : Model,
          normalizer (X : Set Model) =
            sourceSubgroup.map (MulAut.conj g).toMonoidHom) ∨
       (∃ g : Model,
          normalizer (X : Set Model) =
            LinearFive.fullNormalizer.map (MulAut.conj g).toMonoidHom) ∨
       (∃ g : Model,
          normalizer (X : Set Model) =
            max1.map (MulAut.conj g).toMonoidHom) ∨
       (∃ g : Model,
          normalizer (X : Set Model) =
            SymmetricLinear.max4Subgroup.map (MulAut.conj g).toMonoidHom)) := by
  have hlt := larger_four_lt X Y hYX hcardX hYcard
  refine ⟨hlt,?_⟩
  rcases hendpoint with ⟨g,hg⟩ | ⟨g,hg⟩ | ⟨g,hg⟩ | ⟨g,hg⟩
  · left
    exact ⟨g,endpoint_eq_of_le X sourceSubgroup g hmax sourceSubgroup_isTwoLocal
      (hYN.trans hg)⟩
  · right; left
    exact ⟨g,endpoint_eq_of_le X LinearFive.fullNormalizer g hmax
      fullNormalizer_isTwoLocal (hYN.trans hg)⟩
  · right; right; left
    exact ⟨g,endpoint_eq_of_le X max1 g hmax embedded_localKernel_isTwoLocal
      (hYN.trans hg)⟩
  · right; right; right
    exact ⟨g,endpoint_eq_of_le X SymmetricLinear.max4Subgroup g hmax hmax4
      (hYN.trans hg)⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA
