module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Consequences
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Quotient

/-!
# The parameter/component assembly boundary

The output of 11.3.5 retains an actual ambient component, its H-conjugate
span, and its own literal two-core quotient. Its collapse clause covers
exactly k = n or k = 2n, under the already established lower bound.
It is an output specification, not a source hypothesis.

Once 11.3.6 supplies k = n, the assembly identifies this component with
the actual embedded O²(H), retains normality relative to H, and applies
the proved residual/Sylow supplement and outside-local escape.
The source recognition and strict-parameter exclusion are still required;
this module asserts no unconditional 11.3.5 or 11.3.6 theorem.

Source: Aschbacher--Smith, 11.3.5--7(1), printed pp.771--773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The full output needed from 11.3.5, on the actual ambient component.
This definition is a target; no inhabitant is assumed by the source setup. -/
def RankOneReduction (S : D.NonbinaryNaturalInput) (H : Subgroup G) : Prop :=
  ∃ K : Subgroup G, Source.ComponentIn H K ∧
    residual H = Source.conjugateSpan H K ∧
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H) ∧
    (ChapterE.generationParameter H = S.field.degree ∨
      ChapterE.generationParameter H = 2 * S.field.degree → K = residual H)

omit [Finite G] in
/-- The ambient O²(H) is normal relative to H, without recognition. -/
theorem residual_normal (H : Subgroup G) : ((residual H).subgroupOf H).Normal := by
  change ((pResidual 2 H).map H.subtype |>.comap H.subtype).Normal
  rw [comap_map_eq_self_of_injective H.subtype_injective]
  infer_instance

/-- The requested parameter and actual outside-component conclusions. -/
structure Conclusion (S : D.NonbinaryNaturalInput) (H : Subgroup G) : Prop where
  parameter : ChapterE.generationParameter H = S.field.degree
  component : Source.NormalComponentIn H (residual H)
  model : ClassicalGroup.IsPSL ((residual H) ⧸ pCore 2 (residual H)) 2 (2 ^ S.field.degree)
  supplement : H = residual H ⊔ (T : Subgroup G)
  outside : ¬ residual H ≤ normalizer (L : Set G)

/-- Final assembly after recognition and equality have independently been proved.
The output component is O²(H) itself, with its original ambient inclusion. -/
theorem assemble {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H : Subgroup G}
    (h : Hypothesis1131At D S U₁ H)
    (r : RankOneReduction S H)
    (hn : ChapterE.generationParameter H = S.field.degree) : Conclusion S H := by
  obtain ⟨K,hK,_,hmodel,hcollapse⟩ := r
  have he := hcollapse (.inl hn)
  subst K
  refine ⟨hn,⟨hK,residual_normal H⟩,?_,
    (residual_sup_sylow h.outside.1.1.2).symm,residual_outside h⟩
  simpa only [hn] using hmodel

/-- Connect the strict-parameter exclusion to the proved lower bound and the
literal outside component. Recognition and the upper bound are the two
remaining source obligations. -/
theorem assemble_of_parameter_upper {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H : Subgroup G}
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H) (r : RankOneReduction S H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hu : ChapterE.generationParameter H ≤ S.field.degree) : Conclusion S H :=
  assemble h r (Nat.le_antisymm hu (degree_le_parameter h p hc hs))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
