module
public import Theory.SpecificGroups.PSL3Four.ElementaryCubicSplitting
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscape
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesComponent
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightGeometry

/-!
# Faithfulness of the original Cartan in the span action

The action on the larger centralizer span restricts to an action on the
original H-span. Its kernel inside H lies in O₂(H). Thus every odd
subgroup of H embeds under the original centralizer-span projection.
In particular the right Cartan still has order three in that same action.

The Chapter 12 consumer uses this fact with the residual placement of B
and the elementary PSL₃(4) splitting, retaining all original quotient maps.
This does not assert that either factor of the opposite image vanishes.

Source: Aschbacher--Smith 5.1.21--23, printed pp.644--646,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {H C : Subgroup G} {z : G}

/-- The literal quotient kills no element of an odd subgroup of the original H. -/
theorem LocalData.odd_subgroup_image_card (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (B : Subgroup G) (hBH : B ≤ H) (hodd : Odd (Nat.card B)) :
    Nat.card ((B.subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)) =
      Nat.card B := by
  have hHC : H ≤ centralizer ({z} : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  have hdis : Disjoint (B.subgroupOf H) (pCore 2 H) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv,hm]
    exact (Nat.coprime_two_right.mpr hodd).pow_right m
  let f : B →* SpanAction.Actor s :=
    (SpanAction.projection s).comp (inclusion (hBH.trans hHC))
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro b hb
    have hcore : (⟨b,hBH b.property⟩ : H) ∈ pCore 2 H :=
      d.restriction_kernel_le s hHC hb
    have hh : (⟨b,hBH b.property⟩ : H) = 1 :=
      Subgroup.disjoint_def.mp hdis b.property hcore
    exact Subtype.ext (congrArg (fun x : H => (x : G)) hh)
  have hr : f.range = (B.subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s) := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨inclusion (hBH.trans hHC) b,b.property,rfl⟩
    · rintro ⟨b,hb,rfl⟩
      exact ⟨⟨b,hb⟩,rfl⟩
  rw [←hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
