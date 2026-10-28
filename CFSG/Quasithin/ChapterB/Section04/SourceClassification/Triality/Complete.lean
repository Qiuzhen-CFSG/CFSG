module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.Inner.Complete
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.Outer.Source
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Domain
/-!
# Complete triality exclusion on the original B.4.2 action

The genuine inner and outer involution bounds apply to every original faithful
irreducible component action, including all positive field exponents and all
central covers. The actual ambient elementary rank bound excludes an offender.
No model geometry, tensor classification, character-period or earlier-source
premise remains. Source: Aschbacher--Smith B.4.2; Guralnick--Malle II, Lemma 8.6.
-/

public section
open Theory.AlgebraicGroup
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem triality_not_ff
    (h : ChapterK.RankOne.SourceHypotheses ρ L) (n : ℕ) (hn : 0<n)
    (hm : Triality.Standard.IsTrialityGroupAt (2^n) (L ⧸ center L)) :
    ¬ IsFFModule ρ := by
  let := h.quasisimple
  let := h.layer_normal
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp L.subtype)
  let : IsIrreducible ρ := by
    refine ⟨fun S => ?_⟩
    let S' : Subrepresentation (ρ.comp L.subtype) :=
      ⟨S.toSubmodule,fun g v hv => S.apply_mem_toSubmodule g hv⟩
    rcases eq_bot_or_eq_top S' with hs | hs
    · exact Or.inl (Subrepresentation.toSubmodule_injective (congrArg (fun T : Subrepresentation (ρ.comp L.subtype) => T.toSubmodule) hs))
    · exact Or.inr (Subrepresentation.toSubmodule_injective (congrArg (fun T : Subrepresentation (ρ.comp L.subtype) => T.toSubmodule) hs))
  exact ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality.not_ff_of_involution_bounds
    L ρ h.faithful n hn hm
    (ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality.componentInvolutionBound_source n hn hm)
    (ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality.outerInvolutionBound_source L n hn hm)
end CFSG.Quasithin.ChapterB.SourceClassification
