module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Sylow

/-!
# The natural-action paragraph of 11.3.7

The selected active conjugate has its literal star image in the residual and
fills a Sylow subgroup there. Its rank and uniform fixed spaces give the
general G.1.6 recognition hypotheses. Recognition constructs the natural
coordinates with exactly the original global fixed kernel; no splitting or
vanishing of that kernel is required.

Only the preceding source conclusions s(G,V)=n and the PSL2 quotient remain
explicit. Their producers are the natural-local-geometry and
parameter-component owners. The subsequent Cartan argument and final 11.3.7
assembly remain with qt-d-1222-shadow-common-action.

Source: Aschbacher--Smith, 11.3.7, first proof paragraph, printed p.773.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Natural coordinates and the actual selected Sylow image, with Sylow
placement, generation, uniformity and recognition all discharged. -/
theorem selected_natural_action
    (s : Hypothesis1131At D S U₁ H) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)) :
    omegaClosure T H ≤ (T : Subgroup G) ∧
      Nonempty (NaturalQuotientMarking T H S.field) ∧
      ∃ R : Sylow 2 (residualStar T H),
        (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
          ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) ∧
        Representation.BinaryOffender.rank
          (((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H)) =
          S.field.degree ∧
        (∀ a ∈ ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H),
          a ≠ 1 → (starAction T H a).fixedSubgroup =
            (centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)).subgroupOf
              (omegaClosure T H)) ∧
        conjugateSpanBy
          (omegaClosure T H ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G))
          (outsideResidual H) = omegaClosure T H := by
  obtain ⟨R,hR⟩ := selected_star_sylow s g hg ha hs hmodel
  exact ⟨source_omegaClosure_le_sylow s,
    NaturalRecognition.source_naturalQuotientMarking s R g hg hs hmodel hR,
    R,hR,selected_sylow_fixed_and_generated s g hg hs hmodel R hR⟩

open LocalGeometry in
/-- The source flag selects one active conjugate and constructs the marking
and Sylow witness used by the Cartan and transvection consumers. -/
theorem exists_selected_natural_action
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1133 D S (c.binarySubspace (f.space 0)) H)
    (hcounter : ¬ Proposition1132At D S (c.binarySubspace (f.space 0)) H)
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)) :
    omegaClosure T H ≤ (T : Subgroup G) ∧
      Nonempty (NaturalQuotientMarking T H S.field) ∧
      ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
        ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G) ∧
        ∃ R : Sylow 2 (residualStar T H),
          (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
            ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) := by
  obtain ⟨g,hg,ha,R,hR⟩ := exists_selected_star_sylow f s p hcounter hs hmodel
  exact ⟨source_omegaClosure_le_sylow s,
    NaturalRecognition.source_naturalQuotientMarking s R g hg hs hmodel hR,g,hg,ha,R,hR⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
