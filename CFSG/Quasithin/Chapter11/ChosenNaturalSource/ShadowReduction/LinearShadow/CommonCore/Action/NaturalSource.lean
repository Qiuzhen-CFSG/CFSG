module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.FixedSpaces
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Models
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Recognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Recognition.Source

/-!
# Inputs for natural-summand recognition on the original source action

B.2.14 supplies V_H ≤ T and its elementary structure. The residual already
generates its omega orbit, so conjugates of the selected actor's fixed subgroup
generate V_H. A genuine Sylow witness in K-star has rank n; E.3.6 then gives
the same fixed subgroup for every nonidentity element of that actual image.
The quotient matrix model uses the original marked field and projection.
The recognition leaf transports these hypotheses to the literal binary matrix
action and returns any recognized quotient coordinates to the source marking.

The theorem below combines these proved steps with an explicit Sylow witness.
The recognition source leaf now proves `source_naturalQuotientMarking` from
that witness and the preceding parameter and quotient-model conclusions.
The later Cartan and fixed-space clauses of 11.3.7 remain separate obligations.

Source: Aschbacher--Smith, 11.3.7, printed p.773; G.1.6, printed p.329.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The genuine generation and uniformity premises of G.1.6, conditional only
on the separate Sylow placement and the indicated preceding-source conclusions. -/
theorem selected_sylow_fixed_and_generated
    (s : Hypothesis1131At D S U₁ H) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H)) :
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
  have hr := source_residualStar_sylow_rank s hmodel R
  rw [hR] at hr
  exact ⟨hr,fun a ha hne => selected_star_uniform_fixed_of_rank s g hg hs hr a ha hne,
    omegaClosure_generated_by_actor_fixed T H s.outside.1.1.2 _ hg⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
