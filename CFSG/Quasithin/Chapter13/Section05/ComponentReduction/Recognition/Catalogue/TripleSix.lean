module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.TripleSix.Classification
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.TripleSix.SourceConjugation
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Excluding the faithful triple-A₆ constituent in 13.5.21

The chief-image producer supplies a constituent faithful on the ORIGINAL
K*, its component irreducibility, its B.4 hypotheses and its actual Fitting
image equality. Apply the complete corrected B.4.2/B.4.5 disjunction to that
faithful image. The exhaustive comparison retains the triple-six record,
including its actual F₄ coordinates and projective-line offender clause.
The same coordinates give field dimension three and preserve the original
component operators through the literal image map.

The configuration producer supplies V̂ outside K̂ in X/C_X(K*). This gives
non-inner conjugation by the original V* generator. The reusable cover theorem
proves that it moves the cubic Schur operator, so displacement on the faithful
six-space is at least three. The actual section quotient map bounds that rank
by the ambient displacement two, giving the source contradiction.

`excluded_section` retains only the exact universal earlier B.4 implications
and chief-image/configuration premises whose producers are
qt-13-05-catalogue-chief-images and qt-13-05-recognition-configuration. Their
final discharge belongs to qt-13-05-recognition-chief-catalogue. No scalar
inversion, chosen module equivalence, filtered catalogue or split cover is an
input. Centerlessness, simplicity and the remaining catalogue branches are
not asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.2(8),
printed p.86, and 13.5.21, printed p.924 (PDF p.941).
-/

@[expose] public section

open Representation.TripleSixOuterDisplacement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.TripleSix
open Section08.Source

/-- Faithfulness identifies the original component with its actual section
image, and the chief-image producer places precisely this image in F*. -/
noncomputable def fittingEquiv {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (hf : Function.Injective (ρ.comp L.subtype))
    (hfit : actionSubgroup ρ L = generalizedFitting (actionImage ρ)) :
    L ≃* generalizedFitting (actionImage ρ) := by
  have hi : Function.Injective ((actionHom ρ).comp L.subtype) := by
    intro x y hxy
    exact hf (congrArg (imageRepresentation ρ) hxy)
  exact (MonoidHom.ofInjective hi).trans
    (MulEquiv.subgroupCongr ((actionHom_subgroup_range ρ L).trans hfit))

/-- The original component and every original vector retain the literal
section-image action under this equivalence. -/
theorem fittingEquiv_intertwines {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (hf : Function.Injective (ρ.comp L.subtype))
    (hfit : actionSubgroup ρ L = generalizedFitting (actionImage ρ))
    (g : L) (w : W) :
    imageRepresentation ρ (fittingEquiv ρ L hf hfit g) w = ρ (g : E) w := rfl

/-- The corrected coordinates equip the SAME vector space with F₄ scalars
and field dimension three. No quotient by the cubic center is taken. -/
theorem field_finrank {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) E W} {L : Subgroup E}
    (a : ChapterB.SourceInduction.ProjectiveLine.TripleSixAction ρ L) :
    letI := a.coordinates.toAddEquiv.module ChapterB.QuasisimpleSource.BinaryField.four.Carrier
    Module.finrank ChapterB.QuasisimpleSource.BinaryField.four.Carrier W = 3 := by
  let F := ChapterB.QuasisimpleSource.BinaryField.four.Carrier
  let := a.coordinates.toAddEquiv.module F
  let e : W ≃ₗ[F] (Fin 3 → F) := a.coordinates.toAddEquiv.linearEquiv F
  simpa using e.finrank_eq

/-- The cubic-field coordinates commute with the action of the original
component, through the actual faithful-image map. -/
theorem original_scalar_linear {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (hf : Function.Injective (ρ.comp L.subtype))
    (hfit : actionSubgroup ρ L = generalizedFitting (actionImage ρ))
    (a : ChapterB.SourceInduction.ProjectiveLine.TripleSixAction
      (imageRepresentation ρ) (generalizedFitting (actionImage ρ)))
    (g : L) (c : ChapterB.QuasisimpleSource.BinaryField.four.Carrier) (w : W) :
    a.coordinates (ρ (g : E) (a.coordinates.symm (c • a.coordinates w))) =
      c • a.coordinates (ρ (g : E) w) := by
  simpa only [fittingEquiv_intertwines] using
    a.scalar_linear (fittingEquiv ρ L hf hfit g) c w


universe u
variable {G : Type u} [Group G] [Finite G]
    (D : ChapterF.Section09.Setup G) (K : Subgroup G) (h : D.Hypothesis)
    [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- Recognize the faithful constituent using every corrected B.4 alternative.
This returns the full source action record on the literal image; the
preceding intertwining equation retains the ORIGINAL K* and its operators. -/
theorem classified_action (s : Selected D K)
    (hc : Nat.card (center (starImage D.H K)) = 3)
    (q : (starImage D.H K ⧸ center (starImage D.H K)) ≃* alternatingGroup (Fin 6))
    (U N : Subrepresentation (representation D K h))
    (hf : Function.Injective ((chiefRepresentation D K h U N).comp (component D K).subtype))
    (hfit : actionSubgroup (chiefRepresentation D K h U N) (component D K) =
      generalizedFitting (actionImage (chiefRepresentation D K h U N)))
    (hq : quadraticRatio (imageRepresentation (chiefRepresentation D K h U N)) ≤ 2)
    (hall : FullCatalogueAction (imageRepresentation (chiefRepresentation D K h U N))) :
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction
      (imageRepresentation (chiefRepresentation D K h U N))
      (generalizedFitting (actionImage (chiefRepresentation D K h U N)))) := by
  let := s.quasisimple
  obtain ⟨e, _⟩ := cover_equiv hc q
  let c := fittingEquiv (chiefRepresentation D K h U N) (component D K) hf hfit
  exact action_of_fullCatalogue _ (c.symm.trans (componentEquiv.trans e)) hq hall

/-- The literal source-section contradiction: the original outer V* actor
moves at least three dimensions in the faithful triple-cover section, while
the actual quotient map carries down the ambient displacement bound two. -/
theorem excluded_section_of_fullCatalogue (s : Selected D K)
    (hc : Nat.card (center (starImage D.H K)) = 3)
    (q : (starImage D.H K ⧸ center (starImage D.H K)) ≃* alternatingGroup (Fin 6))
    (hnorm : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H)))
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (v : actor D K) (hv : zpowers (v : Hstar D.H) = starImage D.H D.V)
    (hv2 : v ^ 2 = 1)
    (x : X D K) (hx : starHom s h x = (v : Hstar D.H))
    (hout : let := componentCentralizer_normal s h hnorm
      QuotientGroup.mk' (componentCentralizer s h) x ∉
        (K.subgroupOf (X D K)).map (QuotientGroup.mk' (componentCentralizer s h)))
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - 1)) ≤ 2)
    (U N : Subrepresentation (representation D K h))
    (hi : IsIrreducible ((chiefRepresentation D K h U N).comp (component D K).subtype))
    (hf : Function.Injective ((chiefRepresentation D K h U N).comp (component D K).subtype))
    (hfit : actionSubgroup (chiefRepresentation D K h U N) (component D K) =
      generalizedFitting (actionImage (chiefRepresentation D K h U N)))
    (hq : quadraticRatio (imageRepresentation (chiefRepresentation D K h U N)) ≤ 2)
    (hall : FullCatalogueAction (imageRepresentation (chiefRepresentation D K h U N))) : False := by
  let := s.quasisimple
  let : IsQuasisimple (component D K) := IsQuasisimple.of_mulEquiv componentEquiv.symm
  let := hi
  obtain ⟨a⟩ := classified_action D K h s hc q U N hf hfit hq hall
  have hc' : Nat.card (center (component D K)) = 3 :=
    (Nat.card_congr (centerCongr componentEquiv).toEquiv).trans hc
  let q' := (centralQuotientEquiv componentEquiv).trans q
  have hvnorm : (v : Hstar D.H) ∈ normalizer (starImage D.H K : Set (Hstar D.H)) :=
    (s.normalizes_and_commutator h hcard heven).1 (hv ▸ mem_zpowers (v : Hstar D.H))
  have hlower := displacement_ge_three (chiefRepresentation D K h U N) (component D K)
    hc' q' hf a.dimension v (normalizes_component v hvnorm) hv2
    (component_noninner_of_hat_not_mem s h hnorm x v hx hvnorm hout)
  have hupper := fixedCodim_section_le (representation D K h) U N (zpowers v)
  rw [fixedCodim_zpowers_eq_displacement_rank,
    fixedCodim_zpowers_eq_displacement_rank] at hupper
  change Module.finrank (ZMod 2)
      (LinearMap.range (chiefRepresentation D K h U N v - 1)) ≤
    Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - 1)) at hupper
  exact (by decide : ¬ (3 : ℕ) ≤ 2) (hlower.trans (hupper.trans hr))


/-- Apply the two complete corrected source implications to the literal
faithful chief image, then exclude the triple-A₆ case. The chief-image and
source-configuration premises retain their independent producers; neither
a model marking nor scalar inversion is an input to this theorem. -/
theorem excluded_section (s : Selected D K)
    (earlier42 : ChapterB.SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (earlier45 : Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.FullB45.{u,u}
      KnownSimple.IsKnownSimple)
    (hc : Nat.card (center (starImage D.H K)) = 3)
    (q : (starImage D.H K ⧸ center (starImage D.H K)) ≃* alternatingGroup (Fin 6))
    (hnorm : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H)))
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (v : actor D K) (hv : zpowers (v : Hstar D.H) = starImage D.H D.V)
    (hv2 : v ^ 2 = 1)
    (x : X D K) (hx : starHom s h x = (v : Hstar D.H))
    (hout : let := componentCentralizer_normal s h hnorm
      QuotientGroup.mk' (componentCentralizer s h) x ∉
        (K.subgroupOf (X D K)).map (QuotientGroup.mk' (componentCentralizer s h)))
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - 1)) = 2)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (hi : IsIrreducible ((chiefRepresentation D K h U N).comp (component D K).subtype))
    (hf : Function.Injective ((chiefRepresentation D K h U N).comp (component D K).subtype))
    (hfit : actionSubgroup (chiefRepresentation D K h U N) (component D K) =
      generalizedFitting (actionImage (chiefRepresentation D K h U N)))
    (hyp : Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.B4Hypotheses
      KnownSimple.IsKnownSimple (imageRepresentation (chiefRepresentation D K h U N))) : False :=
  excluded_section_of_fullCatalogue D K h s hc q hnorm hcard heven v hv hv2 x hx hout
    hr.le U N hi hf hfit
    (faithful_section_preparation D K h s hcard heven v hv hv2 hr U N hn).2.1
    (classified_section D K h s earlier42 earlier45 hcard heven v hv hv2 hr U N hn hyp)

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.TripleSix
