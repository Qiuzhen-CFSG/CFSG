module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.SourceRecognition
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Irreducibility
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension.Matrix

set_option linter.style.haveILetI false

/-!
# Marked ambient actions in the source M₂₂ branch

The component marking is retained throughout the ambient construction.  For a
simple component, ambient conjugation is transported to `MulAut M22`, and then
to the literal setwise pair stabilizer through the checked equivalence.  The
restriction to the component is the native marked M₂₂ action.  The same file
also records the matrix normalizer interface used for the triple cover; the
normalizer theorem is stated for the literal `actionGroup`, whose derived
subgroup is `M22TripleCover`.

Source: Aschbacher--Smith, Chapter H.13.1 (printed pp.395 and 451/457), and
H.12.1 (printed pp.393--394).
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory Representation
open _root_.Sporadic.Mathieu
open MathieuCode

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The centralizer of a quasisimple M₂₂ component is trivial in the source
ambient group.  The equality `L = F*(G)` is used here, rather than an abstract
group-family tag. -/
theorem source_component_centralizer_eq_bot {L : Subgroup G}
    {ρ : Representation (ZMod 2) G V} (h : SourceHypotheses ρ L)
    (e : L ≃* M22) : centralizer (L : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hle : centralizer (L : Set G) ≤ L := by
    rw [h.component]
    exact centralizer_generalizedFitting_le G
  let xl : L := ⟨x, hle hx⟩
  have hxl : xl ∈ center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using
      (mem_centralizer_iff.mp hx (y : G) y.property)
  have he : e xl = 1 := by
    have hc : e xl ∈ center M22 :=
      (Subgroup.centerCongr e ⟨xl, hxl⟩).property
    rw [Sporadic.Mathieu.m22_center_eq_bot, mem_bot] at hc
    exact hc
  have hxl1 : xl = 1 := e.injective (by simpa using he)
  simpa [xl] using congrArg Subtype.val hxl1

/-- Conjugation on the marked M₂₂ component, transported to the full
automorphism group of M₂₂. -/
def simpleAmbientAutHom (L : Subgroup G) (e : L ≃* M22) (hN : L.Normal) :
    G →* MulAut M22 := by
  letI := hN
  exact (MulAut.congr e).toMonoidHom.comp
    (MulAut.conjNormal (H := L))

theorem simpleAmbientAutHom_injective {L : Subgroup G}
    {ρ : Representation (ZMod 2) G V} (h : SourceHypotheses ρ L)
    (e : L ≃* M22) : Function.Injective
      (simpleAmbientAutHom L e (by rw [h.component]; infer_instance)) := by
  let hN : L.Normal := by
    rw [h.component]
    infer_instance
  letI := hN
  exact (MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot L
      (source_component_centralizer_eq_bot h e))

omit [Finite G] in
theorem simpleAmbientAutHom_on_component {L : Subgroup G}
    (e : L ≃* M22) (hN : L.Normal) (x : L) :
    simpleAmbientAutHom L e hN x = MulAut.conj (e x) := by
  letI := hN
  change (MulAut.congr e) (MulAut.conjNormal (x : G)) = _
  rw [MulAut.conjNormal_val, MulAut.congr_conj]

/-- The same action with the literal setwise pair stabilizer as codomain. -/
def simpleAmbientPairHom (L : Subgroup G) (e : L ≃* M22) (hN : L.Normal) :
    G →* MathieuCode.m22PairStabilizer := by
  letI := hN
  exact m22PairStabilizerEquivAut.symm.toMonoidHom.comp
    (simpleAmbientAutHom L e hN)

theorem simpleAmbientPairHom_injective
    {L : Subgroup G} {ρ : Representation (ZMod 2) G V}
    (h : SourceHypotheses ρ L)
    (e : L ≃* M22) : Function.Injective
      (simpleAmbientPairHom L e (by rw [h.component]; infer_instance)) := by
  let hN : L.Normal := by
    rw [h.component]
    infer_instance
  exact m22PairStabilizerEquivAut.symm.injective.comp
    (simpleAmbientAutHom_injective h e)

omit [Finite G] in
theorem simpleAmbientPairHom_on_component {L : Subgroup G}
    (e : L ≃* M22) (hN : L.Normal) (x : L) :
    simpleAmbientPairHom L e hN x = m22ToPairStabilizer (e x) := by
  letI := hN
  change m22PairStabilizerEquivAut.symm
      (simpleAmbientAutHom L e hN x) = _
  rw [simpleAmbientAutHom_on_component e hN]
  apply m22PairStabilizerEquivAut.injective
  simp

/-- The literal code action carried by the marked ambient homomorphism. -/
def simpleCodeAmbientRepresentation (L : Subgroup G)
    (e : L ≃* M22) (hN : L.Normal) : Representation (ZMod 2) G MathieuCode.M22Code := by
  letI := hN
  exact MathieuCode.m22OuterCodeRepresentation.comp (simpleAmbientPairHom L e hN)

omit [Finite G] in
@[simp] theorem simpleCodeAmbientRepresentation_on_component
    {L : Subgroup G} (e : L ≃* M22) (hN : L.Normal) (x : L)
    (v : MathieuCode.M22Code) :
    simpleCodeAmbientRepresentation L e hN x v = MathieuCode.m22CodeRepresentation (e x) v := by
  change MathieuCode.m22OuterCodeRepresentation
      (simpleAmbientPairHom L e hN x) v = _
  rw [simpleAmbientPairHom_on_component e hN,
    MathieuCode.m22OuterCodeRepresentation_restrict]

/-- The literal cocode action carried by the marked ambient homomorphism. -/
def simpleCocodeAmbientRepresentation (L : Subgroup G)
    (e : L ≃* M22) (hN : L.Normal) : Representation (ZMod 2) G MathieuCode.M22Cocode := by
  letI := hN
  exact MathieuCode.m22OuterCocodeRepresentation.comp (simpleAmbientPairHom L e hN)

omit [Finite G] in
@[simp] theorem simpleCocodeAmbientRepresentation_on_component
    {L : Subgroup G} (e : L ≃* M22) (hN : L.Normal) (x : L)
    (v : MathieuCode.M22Cocode) :
    simpleCocodeAmbientRepresentation L e hN x v = MathieuCode.m22CocodeRepresentation (e x) v := by
  change MathieuCode.m22OuterCocodeRepresentation
      (simpleAmbientPairHom L e hN x) v = _
  rw [simpleAmbientPairHom_on_component e hN]
  rfl

omit [Finite G] in
/-- A chosen source code intertwiner is respected by the marked ambient map on
the component.  This is the representation-level marking used by the source
assembly; no abstract replacement of the component or of its quotient is
introduced. -/
theorem simpleAmbientPairHom_code_intertwining
    {L : Subgroup G} {ρ : Representation (ZMod 2) G V}
    (_h : SourceHypotheses ρ L) (e : L ≃* M22) (hN : L.Normal)
    (E : Representation.Equiv (ρ.comp L.subtype)
      (MathieuCode.m22CodeRepresentation.comp e)) :
    ∀ (x : L) (v : V),
      E (ρ x v) =
        MathieuCode.m22OuterCodeRepresentation (simpleAmbientPairHom L e hN x) (E v) := by
  letI := hN
  intro x v
  rw [simpleAmbientPairHom_on_component e hN]
  change E ((ρ.comp L.subtype) x v) =
    (MathieuCode.m22CodeRepresentation.comp e) x (E v)
  exact LinearMap.congr_fun (E.isIntertwining' x) v

omit [Finite G] in
/-- The cocode version of the marked component intertwiner. -/
theorem simpleAmbientPairHom_cocode_intertwining
    {L : Subgroup G} {ρ : Representation (ZMod 2) G V}
    (_h : SourceHypotheses ρ L) (e : L ≃* M22) (hN : L.Normal)
    (E : Representation.Equiv (ρ.comp L.subtype)
      (MathieuCode.m22CocodeRepresentation.comp e)) :
    ∀ (x : L) (v : V),
      E (ρ x v) =
        MathieuCode.m22OuterCocodeRepresentation (simpleAmbientPairHom L e hN x) (E v) := by
  letI := hN
  intro x v
  rw [simpleAmbientPairHom_on_component e hN]
  change E ((ρ.comp L.subtype) x v) =
    (MathieuCode.m22CocodeRepresentation.comp e) x (E v)
  exact LinearMap.congr_fun (E.isIntertwining' x) v

/- The two permissible image alternatives for the simple marked action.  The
checked design-automorphism theorem supplies the dichotomy; the pair-stabilizer
map above is the same action after the marked equivalence with `MulAut M22`. -/
theorem simpleAmbientDesignHom_image_alternatives
    {L : Subgroup G} {ρ : Representation (ZMod 2) G V}
    (h : SourceHypotheses ρ L) (e : L ≃* M22) :
    (L = ⊤ ∧ Nonempty (G ≃* M22)) ∨
      ∃ f : G ≃* m22DesignAut,
        L.map f.toMonoidHom =
          Sporadic.Mathieu.M22ValueBound.Concrete.inner := by
  letI : L.Normal := by
    rw [h.component]
    infer_instance
  exact Sporadic.Mathieu.M22ValueBound.Concrete.ambient_equiv_alternatives L
    (source_component_centralizer_eq_bot h e) e

namespace TripleAmbient

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

/-- The concrete matrix normalizer used by the triple-cover branch. -/
theorem actionGroupNormalizer :
    Subgroup.normalizer (actionGroup : Set Matrix12ˣ) ≤ actionGroup := by
  exact actionGroup_selfNormalizer

/-- Every element of the literal matrix normalizer therefore has a marked
action in `actionGroup`; this keeps the central extension visible. -/
def restrictNormalizer (x : Subgroup.normalizer (actionGroup : Set Matrix12ˣ)) : actionGroup :=
  ⟨x.1, actionGroupNormalizer x.2⟩

theorem restrictNormalizer_coe (x : Subgroup.normalizer (actionGroup : Set Matrix12ˣ)) :
    (restrictNormalizer x : Matrix12ˣ) = x := rfl

/-- Restriction of the literal normalizer to the checked matrix group. -/
def restrictNormalizerHom :
    Subgroup.normalizer (actionGroup : Set Matrix12ˣ) →* actionGroup where
  toFun := restrictNormalizer
  map_one' := by rfl
  map_mul' x y := by rfl

/-- Any marked normalizer action on the binary twelve-space factors through the
literal `actionGroup`; the derived subgroup remains `M22TripleCover`. -/
def tripleAmbientHom {X : Type*} [Group X]
    (α : X →* Subgroup.normalizer (actionGroup : Set Matrix12ˣ)) :
    X →* actionGroup := restrictNormalizerHom.comp α

theorem tripleAmbientHom_injective {X : Type*} [Group X]
    (α : X →* Subgroup.normalizer (actionGroup : Set Matrix12ˣ))
    (hα : Function.Injective α) : Function.Injective (tripleAmbientHom α) := by
  intro x y hxy
  apply hα
  apply Subtype.ext
  exact congrArg (fun z : actionGroup => (z : Matrix12ˣ)) hxy

/-- The literal binary twelve-space action of the matrix extension. -/
def tripleBinaryAmbientRepresentation :
    Representation (ZMod 2) actionGroup M22TripleCover.BinarySpace :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    ((Units.coeHom Matrix12).comp actionGroup.subtype)

/-- The whole-action representation obtained from a marked normalizer map. -/
def tripleAmbientRepresentation {X : Type*} [Group X]
    (α : X →* Subgroup.normalizer (actionGroup : Set Matrix12ˣ)) :
    Representation (ZMod 2) X M22TripleCover.BinarySpace :=
  tripleBinaryAmbientRepresentation.comp (tripleAmbientHom α)

theorem tripleAmbientRepresentation_intertwining
    {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    (α : X →* Subgroup.normalizer (actionGroup : Set Matrix12ˣ))
    (σ : Representation (ZMod 2) X W)
    (E : Representation.Equiv σ (tripleAmbientRepresentation α)) :
    ∀ (x : X) (v : W), E (σ x v) =
      tripleAmbientRepresentation α x (E v) := by
  intro x v
  exact LinearMap.congr_fun (E.isIntertwining' x) v

@[simp] theorem tripleBinaryAmbientRepresentation_on_derived
    (g : M22TripleCover) (v : M22TripleCover.BinarySpace) :
    tripleBinaryAmbientRepresentation
        (Janko4.InvolutionCentralizers.First.QuotientExtension.coverInclusion g) v =
      M22TripleCover.binaryRepresentation g v := rfl

/-- The nontrivial matrix coset acts on the order-three scalar by inversion.
Under the checked six-dimensional coordinates this is exactly the nontrivial
F₄ field automorphism (`fieldFrobenius`). -/
theorem outerElement_inverts_scalar :
    Janko4.InvolutionCentralizers.First.QuotientExtension.outerElement *
        Janko4.InvolutionCentralizers.First.QuotientExtension.scalarElement *
        Janko4.InvolutionCentralizers.First.QuotientExtension.outerElement⁻¹ =
      Janko4.InvolutionCentralizers.First.QuotientExtension.scalarElement⁻¹ :=
  Janko4.InvolutionCentralizers.First.QuotientExtension.outerElement_conj_scalar

end TripleAmbient

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
