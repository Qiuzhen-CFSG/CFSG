module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Action
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.ComponentAction
public import Theory.Representation.IrreducibleMovedPlaneSections
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.TenDimensional
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.FullCatalogue

/-!
# Literal section actions for the catalogue step of 13.5.21

Restrict the faithful action on U_H/V₁ to the actual K*V*. On every
noncentral section, K* = [K*,V*] makes the distinguished involution act
nontrivially. Its actual action image is faithful and has quadratic ratio
at most two. Once L₁ ≤ K and the source's irreducible marked plane are
available, every such section has displacement exactly two, through the
original quotient map. No identification of K* with K*V* is made.

The full B.4 comparison, the model exclusions, centerlessness, L₁ ≤ K and
the natural chief-module identifications still require their source proofs.
These preparations are not the completed statement of 13.5.21.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.21, printed pp.923–924 (PDF pp.940–941).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open Section08.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (K : Subgroup G)

/-- The source actor K*V*, as a subgroup of the original H/O₂(H). -/
def actor : Subgroup (Hstar D.H) := starImage D.H K ⊔ starImage D.H D.V

/-- The marked component inside K*V*. -/
def component : Subgroup (actor D K) := (starImage D.H K).subgroupOf (actor D K)

/-- The literal L₁-image inside this actor; its containment will be supplied
by the catalogue's group-theoretic argument. -/
noncomputable def localActor : Subgroup (actor D K) := (starImage D.H D.L₁).subgroupOf (actor D K)

/-- Once the source containment is proved, the local actor is the entire
original L₁-image, with no intersection lost. -/
noncomputable def localActorEquiv (hLK : D.L₁ ≤ K) :
    starImage D.H D.L₁ ≃* localActor D K :=
  (subgroupOfEquivOfLe (show starImage D.H D.L₁ ≤ actor D K from
    (map_mono (comap_mono hLK)).trans le_sup_left)).symm

omit [Finite G] in
theorem localActorEquiv_apply (hLK : D.L₁ ≤ K) (l : starImage D.H D.L₁) :
    ((localActorEquiv D K hLK l : actor D K) : Hstar D.H) = (l : Hstar D.H) := rfl

variable (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- No new action is chosen: this is the restriction of Action.starRepresentation. -/
noncomputable def representation :
    Representation (ZMod 2) (actor D K) (Action.Space D) :=
  (Action.starRepresentation D h).comp (actor D K).subtype

theorem representation_injective : Function.Injective (representation D K h) :=
  (Action.starRepresentation_injective D h).comp (actor D K).subtype_injective

/-- An actual linear section U₁/U₂ of U_H/V₁ with its original K*V*-action. -/
noncomputable abbrev chiefRepresentation
    (U N : Subrepresentation (representation D K h)) :=
  sectionRepresentation (representation D K h) U N

/-- Finite dimensionality over F₂ gives the finite carrier required by B.4.5. -/
instance chiefSpace_finite (U N : Subrepresentation (representation D K h)) :
    Finite (N.toSubmodule ⧸ (sectionLower (representation D K h) U N).toSubmodule) :=
  Module.finite_of_finite (ZMod 2)

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
include h in
/-- The proved component commutator identity passes to K*V* under the literal
inclusion, retaining the chosen generator of V*. -/
theorem component_commutator (s : Selected D K)
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (v : actor D K) (hv : zpowers (v : Hstar D.H) = starImage D.H D.V) :
    ⁅component D K, zpowers v⁆ = component D K := by
  apply map_injective (actor D K).subtype_injective
  rw [component, map_commutator, map_subgroupOf_eq_of_le
    (show starImage D.H K ≤ actor D K from le_sup_left), MonoidHom.map_zpowers]
  change ⁅starImage D.H K, zpowers (v : Hstar D.H)⁆ = starImage D.H K
  rw [hv]
  exact (s.normalizes_and_commutator h hcard heven).2

/-- Every section on which the selected component acts nontrivially is moved
by the original distinguished involution. Irreducibility is unnecessary here. -/
theorem noncentral_section_moved (s : Selected D K)
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (v : actor D K) (hv : zpowers (v : Hstar D.H) = starImage D.H D.V)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker) :
    ∃ w, chiefRepresentation D K h U N v w ≠ w :=
  generator_moves_of_noncentral _ (component D K) v
    (component_commutator D K h s hcard heven v hv) hn

/-- The B.4 ratio bound is on the faithful image of the literal section,
with the original actor still mapped into it. This does not assert the
remaining SQTK, Fitting or component-irreducibility premises of B.4. -/
theorem faithful_section_preparation (s : Selected D K)
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (v : actor D K) (hv : zpowers (v : Hstar D.H) = starImage D.H D.V)
    (hv2 : v ^ 2 = 1)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - 1)) = 2)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker) :
    Function.Injective (imageRepresentation (chiefRepresentation D K h U N)) ∧
      quadraticRatio (imageRepresentation (chiefRepresentation D K h U N)) ≤ 2 ∧
      ∀ (g : actor D K) (n : N.toSubmodule),
        imageRepresentation (chiefRepresentation D K h U N) (actionHom (chiefRepresentation D K h U N) g)
          ((sectionLower (representation D K h) U N).toSubmodule.mkQ n) =
        (sectionLower (representation D K h) U N).toSubmodule.mkQ (N.toRepresentation g n) := by
  have hm := noncentral_section_moved D K h s hcard heven v hv U N hn
  exact ⟨imageRepresentation_injective _,
    section_image_ratio_le_two _ U N v hv2 hm hr.le, fun _ _ => rfl⟩

/-- After the independent group argument supplies L₁ ≤ K, condition (iii)
gives the original plane on every noncentral chief section. The displayed
equivalence identifies the actual seed, not merely its dimension. -/
theorem noncentral_section_plane (s : Selected D K)
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (v : actor D K) (hv : zpowers (v : Hstar D.H) = starImage D.H D.V)
    (p : MovedPlane (representation D K h) (localActor D K) v)
    (hseed : p.plane.toSubmodule = Action.seedSpace D)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker) :
    Nonempty (Action.seedSpace D ≃ₗ[ZMod 2]
      LinearMap.range (chiefRepresentation D K h U N v - 1)) ∧
      Module.finrank (ZMod 2) (LinearMap.range (chiefRepresentation D K h U N v - 1)) = 2 ∧
      Module.finrank (ZMod 2) (LinearMap.range (chiefRepresentation D K h U N v - 1)) ≠ 1 := by
  have hm := noncentral_section_moved D K h s hcard heven v hv U N hn
  have hr := p.section_rank U N hm
  exact ⟨⟨(LinearEquiv.ofEq _ _ hseed.symm).trans (p.sectionEquiv U N hm)⟩,
    hr, by rw [show Module.finrank (ZMod 2)
      (LinearMap.range (chiefRepresentation D K h U N v - 1)) = 2 from hr]; decide⟩


/-- The source application of the complete B.4 disjunction. The section-image
hypotheses are precisely the independent chief-action construction obligation;
neither classification implication is specialized to an assumed shortlist. -/
theorem classified_section (s : Selected D K)
    (earlier42 : ChapterB.SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (earlier45 : Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.FullB45.{u,u}
      KnownSimple.IsKnownSimple)
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (v : actor D K) (hv : zpowers (v : Hstar D.H) = starImage D.H D.V)
    (hv2 : v ^ 2 = 1)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - 1)) = 2)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (hyp : Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.B4Hypotheses
      KnownSimple.IsKnownSimple (imageRepresentation (chiefRepresentation D K h U N))) :
    FullCatalogueAction (imageRepresentation (chiefRepresentation D K h U N)) :=
  fullCatalogue_of_sources earlier42 earlier45 _ hyp
    (faithful_section_preparation D K h s hcard heven v hv hv2 hr U N hn).2.1

/-- Concrete exclusion of the ten-dimensional row, on the same original
section and actor. The SL₅ model equivalence is a case assumption to be
obtained from the full catalogue; no exterior-module marking is required. -/
theorem noncentral_section_not_ten (s : Selected D K)
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (v : actor D K) (hv : zpowers (v : Hstar D.H) = starImage D.H D.V)
    (hv2 : v ^ 2 = 1)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - 1)) = 2)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (hi : IsIrreducible (chiefRepresentation D K h U N))
    (e : actor D K ≃* Representation.SL5TenDimensional.Group) :
    Module.finrank (ZMod 2)
      (N.toSubmodule ⧸ (sectionLower (representation D K h) U N).toSubmodule) ≠ 10 := by
  have hm := noncentral_section_moved D K h s hcard heven v hv U N hn
  have hv1 : v ≠ 1 := by
    intro he
    obtain ⟨w, hw⟩ := hm
    exact hw (by simp only [he, map_one, Module.End.one_apply])
  exact TenDimensional.not_ten_dimensional_section _ U N hi e v hv2 hv1 hr.le

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
