module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Selection.Recognition
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.CubicAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
public import CFSG.Quasithin.ChapterA.Section01.Representations.HomogeneousBridge

/-!
# Selecting and recognizing the homogeneous constituent of the reduced cover

We work on the literal conjugation module U_H/V₁ for H/O₂(H), with K* the
actual image of the relatively normal C-component K. The intrinsic cover
isomorphism K/O₂(K) ≃ HexEvenAutomorphisms is transported through the canonical
component comparison. The source identity Y = L₁,+, where Y is the actual
cover residual, gives the primitive cubic polynomial from the seed identity.

A.1.42 selects a genuine homogeneous Irr⁺ member from the existing Irr⁺ seed.
The complete relevant F.9.18(3–4) orbit alternatives are supplied by the
universal `OrbitInvariance.OrbitInputs` interface: the invariant case, the
T-invariant FF case, and the nonisomorphic natural diagram pair. The existing
model separation excludes the last case for the actual triple cover; H = KT
then gives H-invariance. The cubic polynomial kills component-fixed vectors,
so Irr⁺ is irreducible on its original numerator. Component-centralizer
control proves faithfulness, and the orbit action-image ratio transfers to
this exact representation before B.4.5 is applied.

The output retains homogeneity, a faithful actor, the component image, actual
linear intertwining coordinates and dimension six derived from those
coordinates. F.9.18 and the universal irreducible B.4 classifications remain
explicit inputs under this conditional contract. The whole/quotient dichotomy
and final HexacodeSection assembly remain with ModuleRecognition's owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.1.40–42,
printed pp.31–32; B.4.2(8), B.4.5, pp.86–87; F.9.18(3–4), pp.325–326;
13.8.21(2), printed p.956 (PDF p.973).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Selection
open LocalGeometry.DynkinExclusion
universe u

variable {G : Type u} [Group G] [Finite G]

/-- The image of the actual Sylow two-subgroup of H in H/O₂(H). -/
def starSylow (H : Subgroup G) (T : Sylow 2 H) : Sylow 2 (Source.Hstar H) :=
  T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))

/-- The source equality H = KT gives the corresponding generation in H*. -/
theorem star_generation (H K : Subgroup G) (T : Sylow 2 H)
    (hgen : K.subgroupOf H ⊔ (T : Subgroup H) = ⊤) :
    Source.starImage H K ⊔ (starSylow H T : Subgroup (Source.Hstar H)) = ⊤ := by
  change (K.subgroupOf H).map _ ⊔ (T : Subgroup H).map _ = ⊤
  rw [← Subgroup.map_sup, hgen]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

omit [Finite G] in
/-- Relative normality of K in H descends to its actual star image. This
supplies the normality parameter of the public orbit-input contract. -/
theorem starImage_normal (H K : Subgroup G) [(K.subgroupOf H).Normal] :
    (Source.starImage H K).Normal :=
  (inferInstance : (K.subgroupOf H).Normal).map
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
attribute [local instance] starImage_normal

variable (H K V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- In the reduced cover configuration, select an actual T-homogeneous Irr⁺
submodule of U_H/V₁ and recognize its H*-action as the hexacode. The universal
F.9.18(3–4) and irreducible B.4 inputs remain explicit; all three F.9.18
alternatives are considered before obtaining H-invariance. The dimension
follows from the constructed model's coordinates. -/
theorem exists_source_hexacodeModel [Nontrivial (Additive (Source.Utilde H V₃ V₁))]
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
      (starSylow H T) (star_generation H K T hgen))
    (inputs : IrreducibleInputs.{u,u} (Source.starImage H K)) :
    ∃ I : Subrepresentation act.representation,
      Cases.IsIrrPlusWith act.representation (Source.starImage H K) (starSylow H T) I.toSubmodule ∧
      IsIrrPlus act.representation (Source.starImage H K) I.toSubmodule ∧
      Function.Injective I.toRepresentation ∧
      IsIrreducible (I.toRepresentation.comp (Source.starImage H K).subtype) ∧
      Nonempty (HexacodeModel (Source.starImage H K) I.toRepresentation) ∧
      Module.finrank (ZMod 2) I.toSubmodule = 6 := by
  have hseedY : subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H (coverResidualIn K)) = seedSpace H V₃ V₁ := by
    rw [hY]
    exact hseed
  obtain ⟨I₀, hI₀⟩ := exists_source_irrPlus H K V₃ V₁ act hKH hK e hseedY
  have hn : (starSylow H T : Subgroup (Source.Hstar H)) ≤
      normalizer (Source.starImage H K : Set (Source.Hstar H)) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨I, _, hI⟩ := ChapterA.exists_chapter15_isIrrPlusWith_le_orbitSpan
    act.representation hn (starSylow H T).isPGroup' hI₀
  let c := (Components.componentStarEquiv H K hKH hK).symm.trans e
  obtain ⟨z, _, ho, hgenz, hp⟩ :=
    exists_residual_cubic_polynomial H K V₃ V₁ act hKH hK e hseedY
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card
  have hzcenter : zpowers z = (center (Source.starImage H K)).map
      (Source.starImage H K).subtype :=
    hgenz.trans (residual_star_eq_center H K hKH hK hc)
  obtain ⟨J, hJ, hf, hi, hq⟩ := OrbitInvariance.exists_faithful_irreducible_section
    act.representation (Source.starImage H K) (starSylow H T)
    (star_generation H K T hgen) c hcent z ho hzcenter hp src I hI
  obtain ⟨m⟩ := hexacodeModel_of_small_ratio J.toRepresentation (Source.starImage H K) inputs hf hi hq
  exact ⟨J, hJ.symm ▸ hI, hJ.symm ▸ hI.isIrrPlus, hf, hi, ⟨m⟩, m.finrank⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Selection
