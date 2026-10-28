module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.FourComponent.Flags
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.FourComponent.Lifting
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The degree-four local component in 13.8.25

For every marked minimal parabolic in GL₄(2), add an adjacent node. Its
PSL₃(2) quotient lifts through the two-core to a normal local C-component.
The remaining quotient is a two-group, so functoriality of the two-residual
places the original embedded residual inside this component. The actual
full-flag Sylow subgroup normalizes the component through the enlarged
parabolic. The final formula retains the inclusion and both quotient maps.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.25,
printed p.959 (PDF p.976), the assertion supplying K₁ when T_K = T.
Identification of the marked residual with the source L₁ and transport
through H* belong to the source assembly; this module proves the intrinsic
local construction with no such identifications as hypotheses.
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

/-- The original two-perfect residual, embedded in the actual four-dimensional group. -/
noncomputable def fourNodeResidual (b : Basis 3) (i : Fin 3) : Subgroup (LinearGroup 4) :=
  (pResidual 2 (fourParabolic b {i})).map (fourParabolic b {i}).subtype

/-- Every marked single node admits a strictly larger adjacent-node parabolic
and a genuine local C-component containing its embedded two-residual.
The full-flag Sylow subgroup normalizes it, and its intrinsic quotient map
agrees on representatives with the enlarged parabolic's geometric map. -/
theorem four_single_node_component (b : Basis 3) (i : Fin 3) :
    (i.val + 1 = (fourAdjacentNode i).val ∨ (fourAdjacentNode i).val + 1 = i.val) ∧
    fourParabolic b {i} < fourParabolic b {i, fourAdjacentNode i} ∧
    ∃ (K : Subgroup (LinearGroup 4)) (hKP : K ≤ fourParabolic b {i, fourAdjacentNode i}),
      fourNodeResidual b i ≤ K ∧
      (K.subgroupOf (fourParabolic b {i, fourAdjacentNode i})).IsCComponent ∧
      (fourFlagSylow b : Subgroup (LinearGroup 4)) ≤ normalizer K ∧
      ∃ f : (K ⧸ pCore 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2),
        ∀ k : K, f (QuotientGroup.mk' _ k) = fourEnlargedQuotientEquiv b i
          (QuotientGroup.mk' _ (⟨k.val, hKP k.property⟩ : fourParabolic b {i, fourAdjacentNode i})) := by
  let : Finite (LinearGroup 4) := Finite.of_injective
    (fun g : LinearGroup 4 => (g : Space 4 → Space 4)) DFunLike.coe_injective
  obtain ⟨K, hKP, hK, hnorm, hr, f, hf⟩ :=
    BinaryLinear.SmallParabolicLevi.FourComponent.exists_component_of_twoCoreQuotient
      (fourParabolic b {i, fourAdjacentNode i}) (fourEnlargedQuotientEquiv b i)
  refine ⟨fourAdjacentNode_adjacent i, four_single_node_lt b i, K, hKP,
    ?_, hK, ?_, f, hf⟩
  · exact (embedded_pResidual_mono 2 (four_single_node_lt b i).le).trans hr
  · rw [fourFlagSylow_coe]
    exact (fullFlag_le_fourParabolic b _).trans hnorm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
