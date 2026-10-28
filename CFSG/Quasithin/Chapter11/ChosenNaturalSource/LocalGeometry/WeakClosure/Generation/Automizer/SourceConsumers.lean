module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Doubling.Consumers

/-!
# Source generation with the actual automizer bounds discharged

The full natural automizer and doubled V_M calculation supply both bounds
in 11.2.1. The existing doubling theorem supplies the literal two-copy module.
The H-star alternative and the 11.3.6–7 consumers now retain only the exact
odd-kernel normalizer input from the generation argument. Its producer is
qt-d-1222-natural-odd-kernel-normalizer; the weak-closure source and shadow
assembly owners must discharge that premise before claiming the source results.

Source: Aschbacher–Smith 11.2.1, 11.3.6–7, printed pp.766–767,772–773.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The literal generation alternative, conditional only on the shared odd-kernel input. -/
theorem conclusion_of_odd_kernel
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Conclusion D S H :=
  Doubling.conclusion_of_automizer_bounds D S hcontrol (automizerBounds D S) hH

open ShadowReduction
variable {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The actual 11.3.6 parameter exclusion after discharging the automizer bounds. -/
theorem shadow_parameter_upper_of_odd_kernel
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : ParameterComponent.RankOneReduction S H) :
    ChapterE.generationParameter H ≤ S.field.degree :=
  Doubling.shadow_parameter_upper D S hcontrol (automizerBounds D S) h p hc f hpoint r

/-- The literal residual-component application of 11.3.7. -/
theorem shadow_parameter_component_of_odd_kernel
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : ParameterComponent.RankOneReduction S H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ParameterComponent.Conclusion S H :=
  Doubling.shadow_parameter_component D S hcontrol (automizerBounds D S) h p hc f hpoint r hs
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
