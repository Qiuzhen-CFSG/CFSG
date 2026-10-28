module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Doubling.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Source

/-!
# Apply the proved doubling step to the source parameter exclusion

The 11.2.1 assembly supplies the actual doubled module to the checked 11.3.6
contradiction and then to its residual-component application. Only the exact
odd-kernel normalizer and automizer bounds remain from the generation proof.
Their discharge belongs to the weak-closure source owner; the other earlier
shadow premises retain their original assembly owner.
Source: Aschbacher--Smith, 11.2.1 and 11.3.6--7, printed pp.766--767,772--773.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Doubling
open ShadowReduction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The literal 11.3.6 consumer, with doubled recognition and preceding
other-row normalization discharged on the original module. -/
theorem shadow_parameter_upper
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    (hbounds : AutomizerBounds D S)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : ParameterComponent.RankOneReduction S H) :
    ChapterE.generationParameter H ≤ S.field.degree :=
  ParameterComponent.Doubled.source_parameter_upper h p hc f hpoint r
    (conclusion_of_automizer_bounds D S hcontrol hbounds h.outside)

/-- The same generation assembly feeds the actual residual-component
conclusion of 11.3.7, keeping its earlier lower bound explicit. -/
theorem shadow_parameter_component
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    (hbounds : AutomizerBounds D S)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : ParameterComponent.RankOneReduction S H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ParameterComponent.Conclusion S H :=
  ParameterComponent.Doubled.source_parameter_component h p hc f hpoint r
    (conclusion_of_automizer_bounds D S hcontrol hbounds h.outside) hs

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Doubling
