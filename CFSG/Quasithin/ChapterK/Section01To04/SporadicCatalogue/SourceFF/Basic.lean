module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Defs
public import Theory.Representation.BinaryOffender.NormalizerExtension

/-!
# The original B.4 FF action inside its component normalizer

Normality of the literal generalized Fitting subgroup places the faithful
ambient action in the full linear normalizer of its restricted component
action. The same offender transports injectively, so a proved faithful
normalizer exclusion applies to the original source group and module.

This preserves the marked central quotient and all original module data.
Source: Aschbacher--Smith B.4.2, p.86, and K.4, p.457.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

omit [FiniteDimensional (ZMod 2) V] in
theorem source_ff_normalizer (h : RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ) :
    IsFFModule (normalizerRepresentation (ρ.comp L.subtype)) := by
  let : L.Normal := h.layer_normal
  have hi : Function.Injective (actionHom ρ) := by
    intro x y he
    exact h.faithful (congrArg (fun a : actionImage ρ => a.val.val) he)
  apply isFFModule_linearNormalizer ρ L
  exact hff.map_equivariant ρ (imageRepresentation ρ) (actionHom ρ) hi
    (LinearEquiv.refl _ _) (fun _ _ => rfl)

theorem not_ff_of_faithfulExclusion (name : KnownSimple.SporadicName)
    (hx : FaithfulExclusion.{u,v} name) (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* name.Carrier)) : ¬ IsFFModule ρ := by
  let : IsQuasisimple L := h.quasisimple
  intro hff
  exact hx (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective)
    h.irreducible he (source_ff_normalizer h hff)

end CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
