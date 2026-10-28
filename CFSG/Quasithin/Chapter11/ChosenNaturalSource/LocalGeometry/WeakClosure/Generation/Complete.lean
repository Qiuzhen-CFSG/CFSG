module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.ElementaryCoverConsumers

/-!
# The source H-star generation alternative

The proved odd-kernel normalizer theorem makes the literal Hall actor faithful.
The natural and doubled automizer bounds, together with the doubled-module
recognition, then give all alternatives of 11.2.1. The doubled action is on
the original V_M and uses the full quotient L/O₂(L), including its center.
No native-cover, ordinary-module, automizer or doubling premise remains.

The applications supply this generation theorem to the original 11.3.6
parameter bound and 11.3.7 residual-component argument. Their preceding shadow
inputs, original flag and rank-one reduction remain explicit for the shadow
assembly owner; the latter application also retains its earlier lower bound.

Source: Aschbacher--Smith, 11.2.1 and 11.3.6--7, printed pp.766--767,772--773.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Source 11.2.1 on the unchanged chosen natural module, with all generation
inputs discharged. The second alternative retains the full doubled action,
the fixed-space conclusion and the literal Thompson commutator. -/
theorem source_conclusion
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Conclusion D S H :=
  Automizer.conclusion_of_odd_kernel D S
    (OddNormalizer.oddKernelNormalizer_unconditional D S) hH

open ShadowReduction
variable {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Apply the completed 11.2.1 alternative to the literal 11.3.6 parameter
bound, keeping precisely the independently owned preceding shadow inputs. -/
theorem source_shadow_parameter_upper
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : ParameterComponent.RankOneReduction S H) :
    ChapterE.generationParameter H ≤ S.field.degree :=
  ParameterComponent.Doubled.source_parameter_upper h p hc f hpoint r
    (source_conclusion D S h.outside)

/-- Apply the completed generation theorem to 11.3.7 with its original
relative normality, Sylow supplement, quotient maps and residual conclusions. -/
theorem source_shadow_parameter_component
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : ParameterComponent.RankOneReduction S H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ParameterComponent.Conclusion S H :=
  ParameterComponent.Doubled.source_parameter_component h p hc f hpoint r
    (source_conclusion D S h.outside) hs

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
