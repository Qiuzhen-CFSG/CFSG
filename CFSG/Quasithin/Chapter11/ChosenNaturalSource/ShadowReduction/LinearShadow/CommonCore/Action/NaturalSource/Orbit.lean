module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalCoordinates
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Quotient
public import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# The original omega orbit and generation in 11.3.7

The orbit constructed for 11.3.4 is the literal V_H used in the common-core
action. Its reducedness puts it in T and makes it an elementary abelian group.
Since H = KT and T fixes Z, its K-span is already V_H. Consequently the
K-conjugates of C_{V_H}(A) generate V_H for every A ≤ T, including the actual
selected conjugate V^g. This is the generation premise of G.1.6; it needs
neither A = V nor vanishing of C_{V_H}(K).

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.3.4 and 11.3.7, printed pp.771--773; G.1.6, printed p.329.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] (T : Sylow 2 G) (H : Subgroup G)

theorem omegaClosure_eq_parameterOrbit [Finite G] :
    omegaClosure T H = ParameterComponent.omegaOrbit T H := by
  rw [omegaClosure_eq_span, ParameterComponent.omegaOrbit,
    ParameterComponent.sourceZ, omegaCenterIn_eq_omegaOneAmbient]
  rfl

variable [Finite G] {T H} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- B.2.14 on the original subgroup V_H, with the ambient embedding retained. -/
theorem source_omegaClosure_elementary (s : Hypothesis1131At D S U₁ H) :
    IsElementaryAbelian 2 (omegaClosure T H) := by
  rw [omegaClosure_eq_parameterOrbit]
  exact ParameterComponent.omegaOrbit_elementary s

/-- The actual V_H is contained in the original Sylow subgroup. -/
theorem source_omegaClosure_le_sylow (s : Hypothesis1131At D S U₁ H) :
    omegaClosure T H ≤ (T : Subgroup G) := by
  rw [omegaClosure_eq_parameterOrbit]
  exact ParameterComponent.omegaOrbit_le_sylow s

variable (T H)

/-- T fixes the seed and normalizes K, so adjoining T adds no orbit generators. -/
theorem omegaClosure_eq_residual_span (hTH : (T : Subgroup G) ≤ H) :
    omegaClosure T H = conjugateSpanBy (omegaCenter T) (outsideResidual H) := by
  rw [omegaClosure_eq_span]
  apply le_antisymm
  · apply conjugateSpanBy_le (le_conjugateSpanBy _ _)
    nth_rw 1 [← outsideResidual_sup_sylow T H hTH]
    apply sup_le (le_normalizer_conjugateSpanBy _ _)
    apply normalizes_conjugateSpanBy
    · exact (le_centralizer_iff.mp (omegaCenter_le_sylow_centralizer T)).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact hTH.trans (outsideResidual_normalized H)
  · exact conjugateSpanBy_mono le_rfl (outsideResidual_le H)

/-- The precise ambient generation assertion behind the G.1.6 application. -/
theorem omegaClosure_generated_by_actor_fixed (hTH : (T : Subgroup G) ≤ H)
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) :
    conjugateSpanBy (omegaClosure T H ⊓ centralizer (A : Set G))
      (outsideResidual H) = omegaClosure T H := by
  apply le_antisymm
  · exact conjugateSpanBy_le inf_le_left
      ((outsideResidual_le H).trans (omegaClosure_normalized T H))
  · rw [omegaClosure_eq_residual_span T H hTH]
    apply conjugateSpanBy_mono _ le_rfl
    exact le_inf (le_conjugateSpanBy _ _)
      ((omegaCenter_le_sylow_centralizer T).trans (centralizer_le hAT))

variable {T H}

/-- Generation on the chosen source line and the same conjugator selected in
11.3.4. The counterexample is used only to produce an active conjugate. -/
theorem exists_active_conjugate_generating_fixed
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1133 D S (c.binarySubspace (f.space 0)) H)
    (hcounter : ¬ Proposition1132At D S (c.binarySubspace (f.space 0)) H) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G) ∧
      conjugateSpanBy
        (omegaClosure T H ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G))
        (outsideResidual H) = omegaClosure T H := by
  obtain ⟨g,hg,ha⟩ := ParameterComponent.exists_active_conjugate s p hcounter
  refine ⟨g,hg,?_,omegaClosure_generated_by_actor_fixed T H s.outside.1.1.2 _ hg⟩
  simpa only [omegaClosure_eq_parameterOrbit] using ha

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
