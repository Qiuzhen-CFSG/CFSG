module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.SourceDegree
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.MarkedActions
public import Theory.Representation.Mathieu.M22James.Ambient
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.Source

/-!
# Source recognition of the simple and triple M₂₂ modules

The source cubic bound first gives binary degree at most twelve. The genuine
cover reduction and small-module theorems then identify the component with
the degree-ten code or cocode, or the degree-twelve triple-cover module.
Absolute binary rigidity extends the simple intertwiners; the concrete matrix
normalizer extends the triple intertwiner. All three outputs retain the actual
actor, the chosen component marking and the whole-action equivalence.

The triple output also records its central scalar and compatible F₄ coordinates,
with linear inner elements and Frobenius-semilinear outer elements. The exact
Chapter K catalogue application discharges its M₂₂ recognition branch. Local
geometry, offender bounds and ratio calculations are separate results.

Source: Aschbacher–Smith, Chapter K, printed pp.451–452 and 457; H.12–13,
printed pp.393–395; Guralnick–Malle I, Proposition 5.1 and Theorem 6.6/Table 6.7.
See `Source.md` for the primary references and offender-generation conventions.
-/

@[expose] public section
open Sporadic.Mathieu.M22TripleCover.Ambient
open Subgroup Theory.GroupTheory Representation Sporadic.Mathieu MathieuCode
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
noncomputable section

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A simple-cover module with its actual ambient embedding and full-action
intertwiner. The code and cocode are specified by the representation parameter. -/
structure MarkedSimpleModel {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    (σ : Representation (ZMod 2) MathieuCode.m22PairStabilizer W) where
  componentEquiv : L ≃* M22
  embedding : G →* MathieuCode.m22PairStabilizer
  injective : Function.Injective embedding
  on_component : ∀ x : L, embedding x = m22ToPairStabilizer (componentEquiv x)
  component_image : L.map embedding = m22ToPairStabilizer.range
  image : embedding.range = m22ToPairStabilizer.range ∨ embedding.range = ⊤
  equivalence : Representation.Equiv ρ (σ.comp embedding)
  degree : Module.finrank (ZMod 2) V = 10
  ambient : (L = ⊤ ∧ Nonempty (G ≃* M22)) ∨
    ∃ f : G ≃* m22DesignAut,
      L.map f.toMonoidHom = Sporadic.Mathieu.M22ValueBound.Concrete.inner

/-- The genuine triple cover with the actual matrix extension, the chosen
component marking, and compatible F₄ coordinates on the whole action. -/
structure MarkedTripleModel (ρ : Representation (ZMod 2) G V) (L : Subgroup G) where
  componentEquiv : L ≃* M22TripleCover
  embedding : G →* actionGroup
  injective : Function.Injective embedding
  on_component : ∀ x : L, embedding x = coverInclusion (componentEquiv x)
  component_image : L.map embedding = coverSubgroup
  image : embedding.range = coverSubgroup ∨ embedding.range = ⊤
  equivalence : Representation.Equiv ρ (M22TripleCover.Ambient.binaryAction.comp embedding)
  degree : Module.finrank (ZMod 2) V = 12
  coordinates : V ≃ₗ[ZMod 2] M22TripleCover.Unitary.Vector
  intertwines : ∀ g v, coordinates (ρ g v) = tripleFieldAction (embedding g) (coordinates v)
  scalar : ∀ v, coordinates (ρ (componentEquiv.symm M22TripleCover.scalar) v) =
    (QuadraticAlgebra.omega : SL2FourNatural.F) • coordinates v
  inner_linear : ∀ g ∈ L, ∀ (a : SL2FourNatural.F) w,
    coordinates (ρ g (coordinates.symm (a • w))) =
      a • coordinates (ρ g (coordinates.symm w))
  outer_semilinear : ∀ g ∉ L, ∀ (a : SL2FourNatural.F) w,
    coordinates (ρ g (coordinates.symm (a • w))) =
      SL2FourNatural.fieldFrobenius a • coordinates (ρ g (coordinates.symm w))

/-- The three actual modules, including their permitted ambient actions. -/
def MarkedModels (ρ : Representation (ZMod 2) G V) (L : Subgroup G) : Prop :=
  Nonempty (MarkedSimpleModel ρ L m22OuterCodeRepresentation) ∨
  Nonempty (MarkedSimpleModel ρ L m22OuterCocodeRepresentation) ∨
  Nonempty (MarkedTripleModel ρ L)

variable [Finite G] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- The cubic ratio discharges the small-degree premise of component recognition. -/
theorem source_componentModels (h : SourceHypotheses ρ L) :
    ComponentModels (ρ.comp L.subtype) :=
  (source_componentModels_of_degree_le_twelve ρ L h (source_finrank_le_twelve ρ L h)).1

/-- The source module has binary degree ten or twelve. -/
theorem source_finrank_cases (h : SourceHypotheses ρ L) :
    Module.finrank (ZMod 2) V = 10 ∨ Module.finrank (ZMod 2) V = 12 :=
  (source_componentModels_of_degree_le_twelve ρ L h (source_finrank_le_twelve ρ L h)).2

private def sourceTripleModel (h : SourceHypotheses ρ L) (e : L ≃* M22TripleCover)
    (E : Representation.Equiv (ρ.comp L.subtype) (M22TripleCover.representationOfEquiv e)) :
    MarkedTripleModel ρ L := by
  let : L.Normal := by rw [h.component]; infer_instance
  let ι := markedTripleAmbientHom ρ L e E
  let f := E.toLinearEquiv.trans M22TripleCover.Unitary.binaryCoordinates
  have hinter (g : G) (v : V) : f (ρ g v) = tripleFieldAction (ι g) (f v) := by
    change M22TripleCover.Unitary.binaryCoordinates (E (ρ g v)) =
      M22TripleCover.Unitary.binaryCoordinates
        (M22TripleCover.Ambient.binaryAction (ι g)
          (M22TripleCover.Unitary.binaryCoordinates.symm
            (M22TripleCover.Unitary.binaryCoordinates (E v))))
    rw [LinearEquiv.symm_apply_apply, markedTripleAmbientHom_intertwining ρ L e E]
  refine {
    componentEquiv := e
    embedding := ι
    injective := markedTripleAmbientHom_injective ρ L e E h.faithful
    on_component := markedTripleAmbientHom_on_component ρ L e E
    component_image := markedTripleAmbientHom_image ρ L e E
    image := markedTripleAmbientHom_range_cases ρ L e E
    equivalence := Representation.Equiv.mk E.toLinearEquiv
      (fun g => LinearMap.ext (markedTripleAmbientHom_intertwining ρ L e E g))
    degree := E.toLinearEquiv.finrank_eq.trans M22TripleCover.binarySpace_finrank
    coordinates := f
    intertwines := hinter
    scalar := ?_
    inner_linear := ?_
    outer_semilinear := ?_ }
  · intro v
    rw [hinter]
    have he : ι (e.symm M22TripleCover.scalar) = scalarElement := by
      change markedTripleAmbientHom ρ L e E _ = _
      rw [markedTripleAmbientHom_on_component, MulEquiv.apply_symm_apply]
      rfl
    rw [he, tripleFieldAction_scalar]
  · intro g hg a w
    rw [hinter, hinter, f.apply_symm_apply, f.apply_symm_apply]
    exact tripleFieldAction_inner_linear _
      ((markedTripleAmbientHom_mem_cover_iff ρ L e E h.faithful g).mpr hg) a w
  · intro g hg a w
    rw [hinter, hinter, f.apply_symm_apply, f.apply_symm_apply]
    exact tripleFieldAction_outer_semilinear _
      (fun hm => hg ((markedTripleAmbientHom_mem_cover_iff ρ L e E h.faithful g).mp hm)) a w

/-- Full recognition for the actual source actor and representation. Every
numerical, component-recognition, and ambient-extension premise is discharged. -/
theorem source_markedModels (h : SourceHypotheses ρ L) : MarkedModels ρ L := by
  rcases source_componentModels ρ L h with ⟨e, hc | hd⟩ | ⟨e, ⟨E⟩⟩
  · obtain ⟨E⟩ := hc
    refine Or.inr (Or.inl ⟨{
      componentEquiv := e
      embedding := simpleAmbientPairHom L e (by rw [h.component]; infer_instance)
      injective := simpleAmbientPairHom_injective h e
      on_component := simpleAmbientPairHom_on_component e _
      component_image := simpleAmbientPairHom_component_image e _
      image := simpleAmbientPairHom_range_cases e _
      equivalence := sourceCocodeAmbientEquiv h e E
      degree := E.toLinearEquiv.finrank_eq.trans finrank_m22Cocode
      ambient := simpleAmbientDesignHom_image_alternatives h e }⟩)
  · obtain ⟨E⟩ := hd
    exact Or.inl ⟨{
      componentEquiv := e
      embedding := simpleAmbientPairHom L e (by rw [h.component]; infer_instance)
      injective := simpleAmbientPairHom_injective h e
      on_component := simpleAmbientPairHom_on_component e _
      component_image := simpleAmbientPairHom_component_image e _
      image := simpleAmbientPairHom_range_cases e _
      equivalence := sourceCodeAmbientEquiv h e E
      degree := E.toLinearEquiv.finrank_eq.trans finrank_m22Code
      ambient := simpleAmbientDesignHom_image_alternatives h e }⟩
  · exact Or.inr (Or.inr ⟨sourceTripleModel ρ L h e E⟩)

/-- Application to the literal K.4 catalogue inputs, without an extra recognition
or degree premise. This discharges precisely its M₂₂ recognition branch. -/
theorem catalogue_markedModels (h : ChapterK.SporadicCatalogue.SourceHypotheses ρ)
    (hq : Nonempty ((generalizedFitting G ⧸ center (generalizedFitting G)) ≃*
      KnownSimple.SporadicName.m22.Carrier)) :
    MarkedModels ρ (generalizedFitting G) := by
  apply source_markedModels ρ (generalizedFitting G)
  exact {
    sqtk := h.sqtk
    component := rfl
    quasisimple := h.quasisimple
    faithful := h.faithful
    irreducible := h.irreducible
    cubic := h.cubic_le_two
    quotient := hq }

end
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
