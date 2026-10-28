module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.RankOne
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.RankOneExclusions

/-!
# The entire Bender-family alternative in source B.4.2

For the actual central quotient in the Bender list, the PSL2 recognition gives
the natural or symmetric-five row. The unitary and Suzuki branches have
quadratic ratio two and are excluded by the original best offender. All cover,
recognition, ratio and offender premises of this family are discharged.

Source: Aschbacher--Smith Theorem C(3), K.3.1, K.3.3 and K.3.6; B.4.2.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem bender_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ) (hm : ClassificationModels.IsBenderModel (L ⧸ center L)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  cases hm with
  | linear r hr he => exact psl2_case h hff hr he
  | unitary r hr he => exact (not_ff_unitary h hr he hff).elim
  | suzuki m hm he => exact (not_ff_suzuki h hm he.some hff).elim

/-- The literal Bender-family consumer on the original B.4.2 domain. -/
theorem bender_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hm : ClassificationModels.IsBenderModel (L ⧸ center L)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) :=
  bender_case (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA)
    ⟨A,hA.isOffender ρ⟩ hm
end CFSG.Quasithin.ChapterB.SourceClassification
