module
public import Theory.GroupAction.FixedQuotientElementary
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.CheckedCenterAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters

/-!
# The source model supplies the elementary center-commutator layer

The literal U=[Z(O₂(K)),K] lies in the abelian center Z(O₂(K)), and
two-perfection gives [U,K]=U. The specified binary model of U/C_U(K)
therefore forces U itself to be elementary abelian. This applies uniformly
to the natural and doubled source models, including nonshort K.

The final theorem applies the checked center-commutator endgame to that
same source U, removing its separate elementary-layer premise. The source
family still supplies its actual [Z₀,K]=U identity and fixed-space equality.

Source: Aschbacher–Smith, 13.6.22, printed pp.932–933, using C.1.34.
-/

public section
open Subgroup Representation
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
open NonabelianCenters
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
variable {G A W : Type*} [Group G] [Finite G] [Group A]
  [AddCommGroup W] [Module (ZMod 2) W] {K : Subgroup G}
  {ρ : Representation (ZMod 2) A W}

/-- The binary model makes the literal source center commutator elementary. -/
theorem sourceU_elementary_of_model (hp : IsPPerfect 2 K)
    (m : ConjugationQuotientModel K (sourceU K) ρ) :
    IsElementaryAbelian 2 (sourceU K) := by
  have hZ := normalizes_core_center K
  have hUZ : sourceU K ≤ sCenter (K.pCoreIn 2) := by
    rw [sourceU_eq_core_center]
    exact le_normalizer_iff_commutator_le_left.mp hZ
  have hUP : sourceU K ≤ K.pCoreIn 2 :=
    hUZ.trans ((centerIn_eq _).le.trans inf_le_left)
  have hUC : sourceU K ≤ centralizer (K.pCoreIn 2 : Set G) :=
    hUZ.trans ((centerIn_eq _).le.trans inf_le_right)
  let : IsMulCommutative (sourceU K) := le_centralizer_iff_isMulCommutative.mp
    (hUC.trans (centralizer_le hUP))
  apply m.elementary_of_commutator_eq
  rw [sourceU_eq_core_center]
  exact commutator_isPPerfect_idempotent K (sCenter (K.pCoreIn 2)) hp
    ((isPGroup_pCoreIn 2 K).to_le (map_subtype_le _)) hZ

/-- The original model discharges the elementary-layer input to checked averaging. -/
theorem checked_centralizes_of_source_model
    (L K T : Subgroup G) (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hp : IsPPerfect 2 K) (m : ConjugationQuotientModel K (sourceU K) ρ)
    (hcenter : ⁅sourceZ0 K v hK, K⁆ = sourceU K)
    (hn : T ≤ normalizer (K : Set G))
    (S : Sylow 2 (Gv v)) (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = T)
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype ≤ T)
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hLK : Lv L v ≤ K)
    (hfix : sourceU K ⊓ centralizer (Lv L v : Set G) =
      sourceU K ⊓ centralizer (K : Set G))
    (a : Gv v) (haD : (a : G) ∈ centralizer (Lv L v : Set G))
    (ha : checkedQuotientMap v a ∈ centralizer (checkedImage v T : Set (Gcheck v))) :
    K ≤ Gv (a : G) := by
  let : IsElementaryAbelian 2 (sourceU K) := sourceU_elementary_of_model hp m
  exact checked_centralizes_of_center_preimage_commutator L K T (sourceU K) v hK hv hp
    hcenter hn S hS P hP hf hLK hfix a haD ha
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
