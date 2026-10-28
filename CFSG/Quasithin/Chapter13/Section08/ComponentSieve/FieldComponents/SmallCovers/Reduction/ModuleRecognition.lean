module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.Quotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.Residual
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.HexacodeSection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Inputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.ScalarTransport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.CubicAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Selection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Dichotomy

/-!
# Recognizing the actual central-cover section

The source seed identity and relative normality generate U_H/V₁ by the actual
residual Y = L₁,+. Its image is the center of K*, so the genuine cover
identification gives a primitive cubic operator on the whole quotient and on
all its invariant sections.

A.1.42 and all three F.9.18(4) alternatives select an H-invariant Irr⁺ member.
The irreducible B.4.5 input supplies faithful hexacode coordinates on that
member. The complete F.9.18(6) alternatives then give either the whole module
or an FF quotient. Cubic section faithfulness and the proved reducible FF
passage exclude both strong alternatives and recognize the quotient. The
whole-module case is represented by the literal quotient by zero.

`exists_hexacodeSection` constructs the proper denominator, faithful actor
from the actual H/O₂(H), its correct K* image and the linear intertwiner.
`exists_hexacodeSection_of_small_ratio` derives the F.9.18(6) input from the
earlier quadratic-ratio bound. Neither theorem assumes a six-dimensional
section or applies irreducible classification to a reducible module.

The universal earlier B.4 and F.9.18(3–4) statements, together with the reduced
configuration and its component-centralizer bound, remain explicit inputs.
Their discharge and final source-theorem assembly belong to the reduction
owner. For any constructed section, the residual-center transport proves
cubic-scalar placement; `marked_point_of_residual_le` then marks the surviving
seed as an F₄-point with its actual parabolic stabilizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.21(2),
printed p.956 (PDF p.973); B.4.2(8), B.4.5, pp.86–87; F.9.18(3–6), pp.325–326.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable (H K V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

variable {H K V₃ V₁}

/-- Once recognition has been constructed, Y ≤ P supplies the scalar premise
of the existing marked-point theorem. All subgroup images are the actual ones. -/
theorem HexacodeSection.marked_point_of_residual_le
    (act : QuotientAction H V₃ V₁) (s : HexacodeSection H K V₃ V₁ act)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (P : Subgroup G) (hP : P ≤ normalizer (V₃ : Set G))
    (hmax : IsCoatom (Source.starImage H P))
    [IsIrreducible (seedRepresentation H V₃ V₁ act P hP).toRepresentation]
    (hseed : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2)
    (hYP : coverResidualIn K ≤ P) :
    ∃ D : Submodule Hexacode.F hexacode,
      Module.finrank Hexacode.F D = 1 ∧ D.restrictScalars (ZMod 2) = s.seed act ∧
      (subspaceStabilizer Hexacode.action (D.restrictScalars (ZMod 2))).comap s.actor =
        Source.starImage H P :=
  s.marked_point act P hP hmax hseed
    (ModuleRecognition.scalar_mem_of_residual_le H K hKH hK
      s.actor s.actor_injective s.component_image P hYP)

open ModuleRecognition LocalGeometry.DynkinExclusion

variable (H K V₃ V₁)

attribute [local instance] Selection.starImage_normal

/-- Construct the actual six-dimensional section in the reduced triple-cover
configuration. The B.4 and F.9.18 inputs are universal earlier-result contracts;
the denominator, faithful actor, component image and coordinates are outputs. -/
theorem exists_hexacodeSection [Nontrivial (Additive (Source.Utilde H V₃ V₁))]
    (act : QuotientAction H V₃ V₁)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    (hK : (K.subgroupOf H).IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms)
    (T : Sylow 2 H) (hgen : K.subgroupOf H ⊔ (T : Subgroup H) = ⊤)
    (hcent : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≤ Source.starImage H K)
    (L₁plus : Subgroup G) (hY : coverResidualIn K = L₁plus)
    (hseed : subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H L₁plus) = seedSpace H V₃ V₁)
    (src : OrbitInvariance.OrbitInputs act.representation (Source.starImage H K)
      (Selection.starSylow H T) (Selection.star_generation H K T hgen))
    (inputs : IrreducibleInputs.{u,u} (Source.starImage H K))
    (sections : SectionInputs act.representation (Source.starImage H K)) :
    Nonempty (HexacodeSection H K V₃ V₁ act) := by
  obtain ⟨I, _, hI, _, _, ⟨m⟩, _⟩ :=
    Selection.exists_source_hexacodeModel H K V₃ V₁ act hKH hK e T hgen hcent
      L₁plus hY hseed src inputs
  have hseedY : subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H (coverResidualIn K)) = seedSpace H V₃ V₁ := by
    rw [hY]
    exact hseed
  have hYgen := residual_generates_quotient H V₃ V₁ act K hKH hseedY
  have hmove : subspaceCommutator act.representation ⊤ (Source.starImage H K) = ⊤ := by
    apply top_unique
    have hYK : Source.starImage H (coverResidualIn K) ≤ Source.starImage H K :=
      map_mono (fun _ hx => coverResidualIn_le K hx)
    apply hYgen.ge.trans
    apply Submodule.span_mono
    rintro _ ⟨y, hy, v, hv, rfl⟩
    exact ⟨y, hYK hy, v, hv, rfl⟩
  obtain ⟨z, _, ho, hz, hp⟩ :=
    exists_residual_cubic_polynomial H K V₃ V₁ act hKH hK e hseedY
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card
  have hzcenter : zpowers z = (center (Source.starImage H K)).map
      (Source.starImage H K).subtype :=
    hz.trans (residual_star_eq_center H K hKH hK hc)
  let c := (Components.componentStarEquiv H K hKH hK).symm.trans e
  obtain ⟨W, hW, hkind, ⟨q⟩⟩ := exists_hexacode_quotient act.representation
    (Source.starImage H K) c inputs z ho hzcenter hcent hp hmove sections I hI m
  exact ⟨{
    denominator := W
    proper := hW
    denominator_kind := hkind
    actor := q.actor
    actor_injective := q.faithful
    component_image := q.component_image
    equivalence := q.coordinates
    intertwines := q.intertwines }⟩


/-- The earlier quadratic subgroup of ratio at most two supplies the complete
F.9.18(6) section alternatives by the fixed-codimension inequality. -/
theorem exists_hexacodeSection_of_small_ratio
    [Nontrivial (Additive (Source.Utilde H V₃ V₁))]
    (act : QuotientAction H V₃ V₁)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    (hK : (K.subgroupOf H).IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms)
    (T : Sylow 2 H) (hgen : K.subgroupOf H ⊔ (T : Subgroup H) = ⊤)
    (hcent : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≤ Source.starImage H K)
    (L₁plus : Subgroup G) (hY : coverResidualIn K = L₁plus)
    (hseed : subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H L₁plus) = seedSpace H V₃ V₁)
    (src : OrbitInvariance.OrbitInputs act.representation (Source.starImage H K)
      (Selection.starSylow H T) (Selection.star_generation H K T hgen))
    (inputs : IrreducibleInputs.{u,u} (Source.starImage H K))
    (hq : quadraticRatio act.representation ≤ 2) :
    Nonempty (HexacodeSection H K V₃ V₁ act) :=
  exists_hexacodeSection H K V₃ V₁ act hKH hK e T hgen hcent L₁plus hY hseed src inputs
    (sectionInputs_of_small_ratio act.representation (Source.starImage H K) hq)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction
