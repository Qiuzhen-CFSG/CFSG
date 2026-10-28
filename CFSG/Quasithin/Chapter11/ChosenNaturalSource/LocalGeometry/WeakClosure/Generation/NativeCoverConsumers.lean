module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer.SourceConsumers
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.Source

/-!
# Generation and shadow consequences of the native normalizer cover

The uniform J₄ elementary-normalizer cover and the ordinary full-W exclusion
give the exact odd-kernel normalizer theorem. Applying it to the existing
Hall, automizer and doubling argument gives every clause of 11.2.1, with the
original V_M and the full SL₃ action. The same alternative then supplies the
11.3.6 parameter bound and the 11.3.7 residual-component conclusion.

This assembly remains conditional on the native cover, its actual embedded
L₅(2) quotient, and the ordinary full-W exclusion. Their discharge stays with
qt-d-1222-natural-odd-kernel-normalizer and its existing producers; final
11.2.1 discharge stays with qt-d-1222-natural-weak-closure-source. The earlier
shadow hypotheses retain their existing assembly owners. No identification
of the original V with the pushing-up module W is used.

Source: Aschbacher--Smith, 11.2.1 and 11.3.6--7, printed pp.766--767,772--773,
using 4.4.3 and Remark 4.4.2, printed pp.619--623.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
open OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- All source 11.2.1 alternatives from the independent native cover and
ordinary full-module theorem, on the unchanged H-star subgroup. -/
theorem conclusion_of_native_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
    (hordinary : OrdinaryFullModuleExclusion D S)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Conclusion D S H :=
  Automizer.conclusion_of_odd_kernel D S
    (oddKernelNormalizer_of_native_cover D S C eC hcover hordinary) hH

open ShadowReduction
variable {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Apply the assembled generation alternative to the literal 11.3.6 flag
and outside subgroup. The independent earlier shadow inputs remain explicit. -/
theorem shadow_parameter_upper_of_native_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
    (hordinary : OrdinaryFullModuleExclusion D S)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : ParameterComponent.RankOneReduction S H) :
    ChapterE.generationParameter H ≤ S.field.degree :=
  ParameterComponent.Doubled.source_parameter_upper h p hc f hpoint r
    (conclusion_of_native_cover D S C eC hcover hordinary h.outside)

/-- The actual 11.3.7 residual-component application, retaining the same
quotient, relative normality and Sylow supplement as the existing consumer. -/
theorem shadow_parameter_component_of_native_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
    (hordinary : OrdinaryFullModuleExclusion D S)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : ParameterComponent.RankOneReduction S H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ParameterComponent.Conclusion S H :=
  ParameterComponent.Doubled.source_parameter_component h p hc f hpoint r
    (conclusion_of_native_cover D S C eC hcover hordinary h.outside) hs

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
