module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Preparation
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# The literal linear-three branch of original 15.2.23

This interface retains the genuine C.2.3 input on I, R = O₂(M ∩ I),
and NI = M ∩ I, together with precisely the parabolic and MS clauses
of C.2.7(3)(g). In particular the marked parabolic is in the star quotient,
whereas the MS identification is on X/O₂(X). These are distinct maps.

The interface contains no conclusions of the branch exclusion. Earlier
Omega-action, distinguished-factor and Kc clauses are owned by
qt-e-152-char2-component-models, qt-e-152-plane-geometry and
qt-e-152-small-parabolic. The preliminary block reduction and 15.2.21--22
are owned by qt-e-152-char2-block-exclusion and qt-e-152-char2-small-actions.
The former absorbed qt-e-152-block-l3-ms-centralizer on 18 October 2026.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), C.2.7(3)(g)
and the proof of 15.2.23, printed pp.145 and 1116; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

variable {G : Type*} [Group G]

/-- The two literal clauses of C.2.7(g), on its original source input. -/
structure Branch (M I X : Subgroup G) (n : ℕ) (F : Type)
    [Field F] [Finite F] : Prop where
  input : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X
  positive : 1 ≤ n
  field_card : Nat.card F = 2 ^ n
  parabolic : IsLinearMaximalParabolic
    ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
      (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F
  ms : MSDescription KnownSimple.IsKnownSimple X ((M ⊓ I).pCoreIn 2) n F

/-- O₂,Z(X) is the preimage of the center of X/O₂(X), mapped by X → G. -/
abbrev centralCorePreimage (X : Subgroup G) : Subgroup G :=
  (centralPreimage (pCore 2 X)).map X.subtype

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
