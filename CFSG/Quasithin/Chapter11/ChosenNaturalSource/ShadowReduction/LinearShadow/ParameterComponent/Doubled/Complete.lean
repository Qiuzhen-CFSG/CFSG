module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Complete

/-!
# The source parameter equality and residual-component application

The completed 11.2.1 theorem supplies the original generation alternative.
The doubled-source contradiction excludes its strict-parameter branch, and
the preceding E.3.20 lower bound gives k=n, the statement of 11.3.6.
Applying the collapse clause of 11.3.5 identifies its component with the
literal ambient O²(H), retaining relative normality, the actual two-core
quotient, the original Sylow supplement and escape from N_G(L).
The final application realizes K* inside H/C_H(V_H) and records that its
isomorphism from K/O₂(K) commutes with the original projections.

No odd-kernel normalizer, native J₄ cover, generation alternative, doubled
geometry or numerical upper bound is assumed. The authorized 11.3.5
RankOneReduction and earlier global-s lower bound remain explicit for
qt-d-1222-shadow-parameter-component, as do the preceding shadow clauses
and the original invariant flag. This completes the doubled-source
implication, not the independently owned earlier-source discharge.

Source: Aschbacher--Smith, 11.3.6 and 11.3.7(1), printed pp.772--773,
using 11.2.1, printed pp.766--767.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Source 11.3.6 from the independently owned preceding shadow results.
The actual 11.2.1 alternative is constructed on the original D, S and H. -/
theorem source_parameter_eq (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : RankOneReduction S H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ChapterE.generationParameter H = S.field.degree :=
  Nat.le_antisymm
    (source_parameter_upper h p hc f hpoint r
      (LocalGeometry.WeakClosure.Generation.source_conclusion D S h.outside))
    (degree_le_parameter h p hc hs)

/-- Apply 11.3.6 to the actual residual in 11.3.7(1), preserving its
ambient inclusion, relative normality and literal quotient and Sylow data. -/
theorem source_parameter_component_of_preceding (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : RankOneReduction S H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ParameterComponent.Conclusion S H :=
  assemble h r (source_parameter_eq h p hc f hpoint r hs)

/-- The complete 11.3.7(1) application: the actual residual component and
its image in H/C_H(V_H), with the quotient isomorphism commuting with the
literal projections. No action-kernel equality or star-model premise remains. -/
theorem source_parameter_star_of_preceding (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : RankOneReduction S H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ParameterComponent.Conclusion S H ∧
      ClassicalGroup.IsPSL (CommonCore.residualStar T H) 2 (2 ^ S.field.degree) ∧
      ∃ e : (CommonCore.outsideResidual H ⧸ pCore 2 (CommonCore.outsideResidual H)) ≃*
          CommonCore.residualStar T H,
        ∀ k : CommonCore.outsideResidual H,
          (e (QuotientGroup.mk' _ k) : CommonCore.Star T H) =
            CommonCore.starProjection T H (inclusion (CommonCore.outsideResidual_le H) k) := by
  have hr := source_parameter_component_of_preceding h p hc f hpoint r hs
  let := CommonCore.source_residualQuotient_simple (S := S) hr.model
  exact ⟨hr, CommonCore.source_star_model h hr.model,
    CommonCore.residualStarEquiv T H h.outside.1.1.2 h.moves_omega_center,
    CommonCore.residualStarEquiv_apply T H h.outside.1.1.2 h.moves_omega_center⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
