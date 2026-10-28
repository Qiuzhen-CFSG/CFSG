module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.NativeCoverConsumers

/-!
# Generation from the uniform elementary-normalizer cover

The shared ordinary full-W argument and the moved-original-V argument now
use the same native J₄ cover. The odd-normalizer endpoint therefore supplies
Hall faithfulness without a separate ordinary-module exclusion premise.
Applying the established automizer and doubling calculations gives every
11.2.1 alternative on the unchanged V_M and full SL₃ action. Its applications
to 11.3.6 and the residual-component clause of 11.3.7 retain the literal flag,
outside subgroup, quotient maps and earlier shadow hypotheses.

The uniform cover and the embedded local's actual PSL₅(2) quotient remain
independent inputs. Their discharge belongs to
qt-d-1222-natural-odd-kernel-normalizer and its existing native producers;
final 11.2.1 assembly remains with qt-d-1222-natural-weak-closure-source.
These implications do not establish unconditional source completion.

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

/-- All 11.2.1 alternatives with the separate ordinary full-W premise
discharged, retaining the original H-star subgroup and full module. -/
theorem conclusion_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Conclusion D S H :=
  Automizer.conclusion_of_odd_kernel D S
    (oddKernelNormalizer_of_elementary_cover D S C eC hcover) hH

open ShadowReduction
variable {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The literal 11.3.6 parameter bound from the uniform cover alone, with
the independently owned earlier shadow inputs unchanged. -/
theorem shadow_parameter_upper_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : ParameterComponent.RankOneReduction S H) :
    ChapterE.generationParameter H ≤ S.field.degree :=
  ParameterComponent.Doubled.source_parameter_upper h p hc f hpoint r
    (conclusion_of_elementary_cover D S C eC hcover h.outside)

/-- The 11.3.7 residual-component application after discharging the ordinary
full-W premise, preserving the relative normality and Sylow supplement. -/
theorem shadow_parameter_component_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : ParameterComponent.RankOneReduction S H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ParameterComponent.Conclusion S H :=
  ParameterComponent.Doubled.source_parameter_component h p hc f hpoint r
    (conclusion_of_elementary_cover D S C eC hcover h.outside) hs

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
