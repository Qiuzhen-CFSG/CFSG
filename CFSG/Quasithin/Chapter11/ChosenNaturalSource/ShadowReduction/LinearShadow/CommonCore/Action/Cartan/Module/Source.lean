module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Fixed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Orbit

/-!
# The literal moved L-module in the common action

The actual Hall subgroup and natural K-quotient eliminate C_Z(L), C_V(L)
and C_T(L). Sylow averaging then identifies ⟨Z^L⟩ with [Z,L]. Minimality of
the original chosen module gives V ≤ ⟨Z^L⟩; its L-centralizer also vanishes.
These are the original module and inclusions for the remaining B.5.1 and
Cartan calculation, including the possible doubled natural module.

The natural marking and D₀ ≤ L are discharged by the natural-action and
Hall calculations in Action/Source.lean. The remaining L-module comparison
stays with qt-d-1222-shadow-common-action; this lemma does not assert the
vanishing of C_{V_H}(K) or the full source theorem.
Source: Aschbacher--Smith, 11.3.7, printed p.773.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Left fixed-space vanishing and the fully moved original omega orbit.
The actual consumer constructs both the marking and the Hall containment. -/
theorem source_component_module
    (s : Hypothesis1131At D S U₁ H) (c : NaturalQuotientMarking T H S.field)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hAL : oddCartanPart A ≤ L) :
    omegaCenter T ⊓ centralizer (L : Set G) = ⊥ ∧
      V ⊓ centralizer (L : Set G) = ⊥ ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
      V ≤ componentOmegaSpan T L ∧
      componentOmegaSpan T L = ⁅omegaCenter T,L⁆ ∧
      componentOmegaSpan T L ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨hz,hv⟩ := source_left_fixed_spaces s c A hA hHall hAL
  have ht := source_sylow_component_centralizer s c A hA hHall hAL
  have hVU := seed_le_of_contains_omega D S (componentOmegaSpan T L)
    (le_normalizer_conjugateSpanBy _ _) (le_conjugateSpanBy _ _) hv
  have hm : componentOmegaSpan T L = ⁅omegaCenter T,L⁆ := by
    rw [componentOmegaSpan_splitting D S, hz, sup_bot_eq,
      componentOmegaSpan_commutator D S]
  exact ⟨hz,hv,ht,hVU,hm,bot_unique
    ((inf_le_inf_right _ (componentOmegaSpan_le_sylow D S)).trans ht.le)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
