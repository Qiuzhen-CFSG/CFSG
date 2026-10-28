module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.SplitModel
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.PointFusion
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.Basic
public import Theory.SpecificGroups.BinaryLinear.AffinePointCore
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.Quasithin.EvenCharacteristic

/-!
# The exact generalized Fitting core and fusion in the affine source

The marked affine centralizer has a self-centralizing two-core, so its
intrinsic generalized Fitting subgroup is that two-core. Transporting this
fact through the original marking puts the previously constructed point
fusion into the exact core used by I.4.6. The chosen module supplies an
actual nonidentity involution, with a conjugator in the original L.

The extraspecial structure, S₃ quotient, Sylow-three fixed subgroup and
quaternion nonnormality still require the dimension-three local calculation;
this module does not assert the full I.4.6 hypotheses. Their construction
and final source application remain with qt-d-12213-three-recognition.
Source: Aschbacher–Smith 12.2.27(2) and I.4.6, printed pp.807,417.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.SplitLinearConfiguration
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}
variable (C : SplitLinearConfiguration L V d)
include C

theorem point_generalizedFitting_eq_pCore (hnone : NoEscape L V)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    generalizedFitting (centralizer ({v} : Set G)) = pCore 2 (centralizer ({v} : Set G)) := by
  obtain ⟨w, _, E, _⟩ := C.exists_point_centralizer_model hnone hv hv1
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 E).mpr
    (BinaryLinear.Affine.point_core_selfCentralizing d w)

theorem point_fused_in_generalizedFitting (D : ChosenModule T L V)
    (hnone : NoEscape L V) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    ∃ l ∈ L, l * v * l⁻¹ ∈ Extraspecial32.coreInG v ∧ l * v * l⁻¹ ≠ v := by
  change ∃ l ∈ L, l * v * l⁻¹ ∈
    (generalizedFitting (centralizer ({v} : Set G))).map
      (centralizer ({v} : Set G)).subtype ∧ _
  rw [C.point_generalizedFitting_eq_pCore hnone hv hv1]
  exact C.point_fused_in_core D hnone hv hv1

/-- The original chosen module supplies a fused involution and the exact core convention. -/
theorem exists_fused_point_generalizedFitting (D : ChosenModule T L V)
    (hnone : NoEscape L V) :
    ∃ v : G, v ∈ V ∧ orderOf v = 2 ∧
      Extraspecial32.Core v = pCore 2 (Extraspecial32.Centralizer v) ∧
      ∃ l ∈ L, l * v * l⁻¹ ∈ Extraspecial32.coreInG v ∧ l * v * l⁻¹ ≠ v := by
  obtain ⟨v, hv, hv1⟩ := V.bot_or_exists_ne_one.resolve_left D.ne_bot
  let := D.elementary
  exact ⟨v, hv, orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv) hv1,
    C.point_generalizedFitting_eq_pCore hnone hv hv1,
    C.point_fused_in_generalizedFitting D hnone hv hv1⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.SplitLinearConfiguration
