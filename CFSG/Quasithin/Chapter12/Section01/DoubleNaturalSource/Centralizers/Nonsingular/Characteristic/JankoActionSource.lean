module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.JankoAction
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FourStarFixedSource

/-!
# Applying the original J4 point-join reduction

The original ordinary-component alternative supplies a concrete subgroup
of the actual J4 model, its elementary moving subgroup, the full point
automizer quotient, and the literal core centralization and commutator
relations. The finite local-model exclusion below is a sufficient input;
its proof remains with qt-d-double-natural-centralizers. The stronger
source action and its canonical quotient map remain in JankoAction.

The conditional applications run nonsingular control before degree-five
closure and the pure-point family, and run degree-four closure last. The
marked MS premise remains with qt-d-double-natural-pure-fusion and
qt-rank-two-ms93. Final assembly retains these obligations; no theorem in
this module asserts their discharge.
Source: Aschbacher--Smith 12.1.1--7, printed pp.788--792.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
/-- A concrete local configuration in the actual J4 carrier. The core quotient
is the full point automizer. Full ambient Sylow containment is required only
in degree four, where the original source proves it. No exclusion is asserted. -/
@[expose] def JankoPointJoinModel (n : ℕ) : Prop :=
  ∃ H E : Subgroup Janko4.Model,
    E ≤ H ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 2^(2*(n-1)) ∧
    H ≤ normalizer (E : Set Janko4.Model) ∧
    H.pCoreIn 2 ≤ centralizer (E : Set Janko4.Model) ∧ E = ⁅E,H⁆ ∧
    Nonempty ((H ⧸ pCore 2 H) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin (n-1)) (ZMod 2))) ∧
    (n = 4 → ∃ P : Sylow 2 Janko4.Model, (P : Subgroup Janko4.Model) ≤ H)
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The ordinary J4 alternative constructs a genuine local model, with the
image coming from the literal point-residual/Sylow join. -/
theorem doubleNatural_adapted_jankoFour_pointJoin_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) → Nonsingular.JankoPointJoinModel n := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK ⟨e⟩
  obtain ⟨r,_,_,_,he,hel,hcard,hn,hcore,hm,hS⟩ :=
    D.doubleNatural_adapted_jankoFour_pointJoin_image h B S w hw K hK e
  exact ⟨r.range,_,map_le_range r _,hel,hcard,hn,hcore,hm,he,hS⟩

/-- Conditional original nonsingular and degree-five closure assembly.
The finite J4 local-model exclusion is an explicit remaining obligation. -/
theorem doubleNatural_nonsingular_controls_of_no_jankoFour_pointJoin_model_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hj : ¬ Nonsingular.JankoPointJoinModel n) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  apply D.doubleNatural_nonsingular_controls_of_jankoFour_of_many h hmany B
  intro S w hw K hK _ _ _ he
  exact hj (D.doubleNatural_adapted_jankoFour_pointJoin_model h B S w hw K hK he)

/-- All three original conclusions in degree five, conditional only on the
remaining intrinsic J4 model exclusion; no degree-four Sylow is inserted. -/
theorem doubleNatural_five_conclusions_of_no_jankoFour_pointJoin_model_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) (hj : ¬ Nonsingular.JankoPointJoinModel 5) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers ∧ B.PureIntersectionCentralizes ∧
      0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  apply D.doubleNatural_five_conclusions_of_jankoFour_of_many h hmany B
  intro S w hw K hK _ _ _ he
  exact hj (D.doubleNatural_adapted_jankoFour_pointJoin_model h B S w hw K hK he)

/-- Source-order assembly retains the finite J4 exclusion and the existing
marked MS premise in degree four. Neither premise is asserted here. -/
theorem doubleNatural_conclusions_of_no_jankoFour_pointJoin_model_of_omega_fixed_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hj : ¬ Nonsingular.JankoPointJoinModel n) :
    letI := D.doubledOrbit_elementary h
    (n = 4 → ∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    B.NonsingularCentralizers ∧ B.PureIntersectionCentralizes ∧
      0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  apply D.doubleNatural_conclusions_of_jankoFour_of_omega_fixed_of_many h hmany B _ hfixed
  intro S w hw K hK _ _ _ he
  exact hj (D.doubleNatural_adapted_jankoFour_pointJoin_model h B S w hw K hK he)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
