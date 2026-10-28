module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural.Images
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Models
public import Theory.SpecificGroups.BinaryLinear.TransvectionCubicCentralizer

/-!
# The linear-model sieve in the split branch of 15.3.58

A natural binary linear model identifies both the actor and its vector
space. Transporting the marked displacement through those coordinates
preserves its rank. In dimensions four and five the intrinsic transvection
centralizer contains an element of order three in the derived subgroup;
transporting it back contradicts the explicit cubic-centralizer restriction.
The given lower dimension bound also excludes dimension two, leaving the
actual dimension-three action model.

The restriction on commuting cubic elements is an explicit premise here.
The source assembly must obtain it from the displacement-plane stabilizer
and transport through the constituent kernel. This module does not assert
that those further premises have been discharged.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.6.4,
printed pp.345–346, and the first split-constituent paragraph in the proof
of 15.3.58, printed p.1149.
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural.LinearSieve

variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

private theorem model_rank (σ : Representation (ZMod 2) A E) (t : A) {n : ℕ}
    (eA : A ≃* BinaryLinear.GL (Fin n → ZMod 2))
    (eE : E ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (he : ∀ a v, eE (σ a v) = linearRepresentation n (eA a) (eE v)) :
    Module.finrank (ZMod 2) (LinearMap.range ((eA t).toLinearMap - LinearMap.id)) =
      Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) := by
  have hd : (eA t).toLinearMap - LinearMap.id =
      (eE.toLinearMap.comp (σ t - LinearMap.id)).comp eE.symm.toLinearMap := by
    apply LinearMap.ext
    intro w
    change eA t w - w = eE (σ t (eE.symm w) - eE.symm w)
    rw [map_sub, he, eE.apply_symm_apply]
    rfl
  rw [hd, LinearMap.range_comp_of_range_eq_top _ eE.symm.range,
    LinearMap.range_comp, eE.finrank_map_eq]

/-- The cubic-centralizer obstruction excludes every linear alternative except
three, retaining the actual group and module identifications. -/
theorem linear_model_eq_three [Finite A] [Finite E]
    (σ : Representation (ZMod 2) A E) (t : A)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) = 1)
    (hdim : 3 ≤ Module.finrank (ZMod 2) E)
    (hno : ∀ c ∈ commutator A, orderOf c = 3 → ¬ Commute c t)
    {n : ℕ} (hn₂ : 2 ≤ n) (hn₅ : n ≤ 5)
    (hmodel : HasActionModel σ (linearRepresentation n)) :
    n = 3 ∧ HasActionModel σ (linearRepresentation 3) := by
  obtain ⟨eA, eE, he⟩ := hmodel
  have hdimn : Module.finrank (ZMod 2) E = n := by simpa using eE.finrank_eq
  have hn₃ : 3 ≤ n := by omega
  have hnot : ¬ 4 ≤ n := by
    intro hn₄
    obtain ⟨c, hc, ho, ht⟩ :=
      BinaryLinear.TransvectionCubicCentralizer.exists_order_three_mem_commutator_commute
        hn₄ (eA t) ((model_rank σ t eA eE he).trans hr)
    have hmem : eA.symm c ∈ commutator A := by
      have hh := mem_map_of_mem eA.symm.toMonoidHom hc
      rw [map_commutator_eq, eA.symm.toMonoidHom.range_eq_top_of_surjective eA.symm.surjective] at hh
      exact hh
    have hcomm : Commute (eA.symm c) t := by
      have hh : Commute (eA.symm c) (eA.symm (eA t)) := ht.map eA.symm.toMonoidHom
      simpa only [eA.symm_apply_apply] using hh
    exact hno (eA.symm c) hmem ((eA.symm.orderOf_eq c).trans ho) hcomm
  have hn : n = 3 := by omega
  refine ⟨hn, ?_⟩
  rw [← hn]
  exact ⟨eA, eE, he⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural.LinearSieve
