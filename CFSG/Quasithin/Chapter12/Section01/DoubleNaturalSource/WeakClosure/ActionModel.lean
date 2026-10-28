module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ActionModel.Quotient
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Model
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry

/-!
# The compatible doubled-orbit model and the second weak-closure bound

The quotient model is constructed from the original component action and
transported through the literal normalizer-action quotient. Its automizer
representation and its two summands are exactly the ones used by E.3.32.
Thus the H.9 degree-four and degree-five core calculations give 12.1.10
without an additional model premise. The first-stage bound remains the
separate offender argument of 12.1.8.

Source: Aschbacher--Smith, H.9 and 12.1.10, printed pp.389--392,794.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- The constructed H.9 model on the actual ambient automizer. -/
def markedAutomizerModel
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G)) :
    B.MarkedAutomizerModel :=
  B.sourceModel.automizerModel hNM

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
include h D

/-- Construct the compatible model from the chosen module's normalizer theorem. -/
def doubled_markedAutomizerModel {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    B.MarkedAutomizerModel := by
  letI := D.doubledOrbit_elementary h
  exact B.markedAutomizerModel (D.doubledOrbit_normalizer_eq h B.orbit_eq)

theorem doubled_nonempty_markedAutomizerModel {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    Nonempty B.MarkedAutomizerModel :=
  ⟨D.doubled_markedAutomizerModel h B⟩

/-- Both conditional weak-closure implications of 12.1.10, with the model
constructed and all its compatibility premises discharged. -/
theorem doubled_globalW_gt_two_of_many {n : ℕ}
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    1 < globalW (componentOrbit V (T : Subgroup G)) T →
    ((n + 2 : ℕ) : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
    2 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  exact D.doubled_globalW_gt_two_of_many_of_model h hmany B
    (D.doubled_markedAutomizerModel h B)

/-- The degree-five consumer of the constructed compatible model. -/
theorem doubledFive_globalW_gt_two_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    1 < globalW (componentOrbit V (T : Subgroup G)) T →
    (7 : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
    2 < globalW (componentOrbit V (T : Subgroup G)) T :=
  D.doubled_globalW_gt_two_of_many h hmany B

/-- The degree-four consumer of the constructed compatible model. -/
theorem doubledFour_globalW_gt_two_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    1 < globalW (componentOrbit V (T : Subgroup G)) T →
    (6 : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
    2 < globalW (componentOrbit V (T : Subgroup G)) T :=
  D.doubled_globalW_gt_two_of_many h hmany B

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
