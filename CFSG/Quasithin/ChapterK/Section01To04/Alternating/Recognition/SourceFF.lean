module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.FourSpace
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Normalizer
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSixDegree
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSevenExclusion
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Hexacode
public import Theory.Representation.BinaryAlternatingSixSmallDegrees

/-!+# Alternating representation recognition for the original FF input

For an A₆ component, the proved ambient conjugate-generation bound and an
actual offender give binary degree at most six. The small-degree orbit
argument then forces degree four. Intrinsic four-space recognition and its
linear normalizer recover the natural action and its marked S₆ extension.
Together with the proved A₇ and triple-cover branches this recognizes every
alternating action required by B.4.2, without any module catalogue premise.

Source: Aschbacher–Smith, K.1–K.1.3, printed pp.452–453, applied to the FF
hypothesis of B.4.2. The larger cubic-ratio-two A₆ degree problem remains
separate; this theorem uses the actual offender present in the source consumer.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterK.Alternating

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}} {L : Subgroup G}

/-- An actual ambient offender sharpens the A₆ conjugate-generation estimate
to degree six; no restriction of the offender to the component is used. -/
theorem six_finrank_le_six_of_ff (h : Input ρ K L)
    (e : L ≃* alternatingGroup (Fin 6)) (hff : IsFFModule ρ) :
    Module.finrank (ZMod 2) V ≤ 6 := by
  obtain ⟨A, hA, hsmall⟩ := hff
  obtain ⟨n, g, hn, hg⟩ := SixDegreeReduction.actorGeneration L h.fitting e A hA
  let : IsSimpleGroup (L ⧸ center L) := h.quasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hd := finrank_le_card_mul_fixedCodim_of_subgroup_conjugates ρ L A
    (fixedSpace_eq_bot_of_faithful_irreducible_on ρ L h.faithful h.irreducible) g hg
  simp only [Fintype.card_fin] at hd
  exact hd.trans ((Nat.mul_le_mul_left n hsmall).trans hn)

/-- The faithful A₆ component has degree four under the source FF hypothesis. -/
theorem six_finrank_eq_four_of_ff (h : Input ρ K L)
    (e : L ≃* alternatingGroup (Fin 6)) (hff : IsFFModule ρ) :
    Module.finrank (ZMod 2) V = 4 := by
  let τ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  have hd := AlternatingSix.BinarySmallDegrees.finrank_eq_one_or_four τ
    (six_finrank_le_six_of_ff ρ h e hff)
  have hlo := four_le_finrank_of_six_component ρ h e
  omega

/-- The full marked A₆ natural action is constructed from the original FF input. -/
theorem six_naturalAction_of_ff (h : Input ρ K L)
    (e : L ≃* alternatingGroup (Fin 6)) (hff : IsFFModule ρ) :
    Nonempty (NaturalAction ρ L 6) :=
  six_naturalAction_of_dimension RecognitionInputs.Six.fourSpace
    RecognitionInputs.Six.normalizer ρ h e (six_finrank_eq_four_of_ff ρ h e hff)

/-- Actual alternating module recognition for B.4.2. Every actor, intertwiner,
and permitted ambient extension is constructed from the source input. -/
theorem recognition_of_ff (h : Input ρ K L) (hff : IsFFModule ρ) :
    RecognizedAction ρ L := by
  rcases h.cover_alternatives with he | he | he | he
  · obtain ⟨e⟩ := he
    obtain ⟨a⟩ := six_naturalAction_of_ff ρ h e hff
    exact .six a
  · obtain ⟨e⟩ := he
    rcases sevenRecognition ρ K L h e with ha | ha
    · obtain ⟨a⟩ := ha
      exact .sevenNatural a
    · obtain ⟨hL, ⟨a⟩⟩ := ha
      exact .sevenFour hL a
  · obtain ⟨e⟩ := he
    obtain ⟨a⟩ := hexacodeAction_of_dimension ρ h e (tripleSixDegree ρ K L h e)
    exact .tripleSix a
  · obtain ⟨_, ⟨e⟩⟩ := he
    exact (tripleSevenExclusion ρ K L h e).elim

end CFSG.Quasithin.ChapterK.Alternating
