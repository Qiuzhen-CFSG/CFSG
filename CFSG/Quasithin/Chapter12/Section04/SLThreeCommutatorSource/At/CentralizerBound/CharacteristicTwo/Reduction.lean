module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.CharacteristicTwo.Contracts
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Preparation
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.CommonNormalKnownSimple

/-!
# The E.6.14 dichotomy on the literal L₃ hyperplane

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

The normalizer of the selected residual block lies above the maximal
hyperplane stabilizer in LT. If it is that stabilizer, the localized index
calculation contradicts the geometric index. If it is all of LT, the fixed
subspace C_V(J) is T-invariant and escapes M, contradicting the proved E.6.13.
The common-normal input is discharged by original known-simple 3.1.1.

This is conditional assembly over the contracts in Contracts.lean.
Application.lean discharges the geometry; block selection and the local
index calculation remain source obligations.
Source: Aschbacher–Smith, E.6.14, printed p.251, applied in 12.4.8, p.815.
-/

public section
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.CharacteristicTwo
open ChapterE ChapterE.Section06 ChapterE.Section06.InvariantSubspaces
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- The two normalizer alternatives for the actual selected block. No
common-normal theorem or global block-selection callback is assumed. -/
theorem false_of_singleBlock (c : Configuration T L V U)
    (hc : HasCharacteristicTwo (centralizer (U : Set G)))
    (geometry : StabilizerGeometry T L U) (index : BlockIndex c)
    (J : Subgroup G) (hJ : SingleBlock T (normalizer (V : Set G)) V U J)
    (hAlt : ChapterC.IsAlternatingBlock J 3 ∨ ChapterC.IsAlternatingBlock J 5) : False := by
  let A := L ⊔ (T : Subgroup G)
  let M := normalizer (V : Set G)
  have hE := source_hypothesisE61 c.hypothesis c.structural c.extension c.fixed_nontrivial
  have hU := (escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape).2.2.2.1
  have hJM : ¬ J ≤ M := by
    intro hj
    apply c.escape
    rw [hJ.generated]
    exact sup_le inf_le_right hj
  have hn : normalizer (U : Set G) ≤ normalizer (J : Set G) := by
    rw [hJ.residual_three]
    exact (normalizer_le_normalizer_centralizer U).trans
      (normalizer_le_normalizer_characteristic_image (centralizer (U : Set G))
        (primeToResidual 3 (centralizer (U : Set G))))
  have hbetween : localNormalizer A U ≤ localNormalizer A J := inf_le_inf_left A hn
  rcases geometry.maximal.eq_or_eq hbetween inf_le_left with he | he
  · exact geometry.index_ne_two (he ▸ index hc J hJ hAlt (he.symm ▸ geometry.maximal))
  · let W := V ⊓ centralizer (J : Set G)
    have hUW : U ≤ W := le_inf c.le_module (le_centralizer_iff.mp hJ.le_centralizer)
    have hWne : W ≠ ⊥ := fun hb => hU.2.1 (le_bot_iff.mp (hb ▸ hUW))
    have hAJ : A ≤ normalizer (J : Set G) := he.ge.trans inf_le_right
    have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
      (le_inf hE.sylow_le_normalizer
        (((show (T : Subgroup G) ≤ A from le_sup_right).trans hAJ).trans
          (normalizer_le_normalizer_centralizer J))).trans
        inf_normalizer_le_normalizer_inf
    have hWnormal : (W.subgroupOf (T : Subgroup G)).Normal :=
      (normal_subgroupOf_iff_le_normalizer
        ((show W ≤ V from inf_le_left).trans hE.le_sylow)).mpr hTW
    have hC := centralizer_le_of_normal_in_sylow_knownSimple hE hWne inf_le_left
      (oddCentralizerCondition_mono hUW hU.2.2.2) hWnormal
    exact hJM ((le_centralizer_iff.mpr
      (show W ≤ centralizer (J : Set G) from inf_le_right)).trans hC)

/-- Actual source application of the independently constructed geometry,
block selection and localized index calculation. -/
theorem false_of_inputs (c : Configuration T L V U)
    (hc : HasCharacteristicTwo (centralizer (U : Set G)))
    (geometry : StabilizerGeometry T L U)
    (selection : BlockSelection c) (index : BlockIndex c) : False := by
  obtain ⟨J, hJ, hAlt⟩ := selection hc geometry.faithful_three
  exact false_of_singleBlock c hc geometry index J hJ hAlt

/-- Assembly into the unchanged case contract. The explicit premises are
not assertions that all source obligations have been completed. -/
theorem characteristicTwoExclusion_of_inputs
    (geometry : ∀ (G : Type u) [Group G] [Finite G]
      (T : Sylow 2 G) (L V U : Subgroup G), Configuration T L V U →
        StabilizerGeometry T L U)
    (selection : ∀ (G : Type u) [Group G] [Finite G]
      (T : Sylow 2 G) (L V U : Subgroup G) (c : Configuration T L V U), BlockSelection c)
    (index : ∀ (G : Type u) [Group G] [Finite G]
      (T : Sylow 2 G) (L V U : Subgroup G) (c : Configuration T L V U), BlockIndex c) :
    CharacteristicTwoExclusion.{u} := by
  intro G _ _ T L V U c hc
  exact false_of_inputs c hc (geometry G T L V U c)
    (selection G T L V U c) (index G T L V U c)

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.CharacteristicTwo
