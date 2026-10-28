module

public import Theory.Representation.Mathieu.M22James
public import Theory.Representation.Mathieu.M22James.Unitary.Action
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension.Matrix

/-!
# Marked ambient actions on the genuine triple Mathieu module

Perfectness and full quotient-automorphism coverage reduce every matrix
normalizing the derived group to the checked scalar centralizer. Thus the
normalizer is the literal matrix extension `actionGroup`. Transporting any
normal component action along its chosen intertwiner constructs an ambient
embedding, preserving the component marking and every vector action.

The native six-dimensional F₄ coordinates make the component linear. Every
outer matrix inverts the central cubic scalar, so it is Frobenius-semilinear.
The image alternatives retain the actual extension, rather than its group of
automorphisms or its central quotient.

Source: Aschbacher–Smith H.12.1, printed pp.393–394. The native matrices and
ATLAS attribution are retained in the imported `LinearModel/source/` files.
-/

@[expose] public section
open scoped Matrix
open Subgroup Theory.GroupTheory Representation Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
namespace Sporadic.Mathieu.M22TripleCover.Ambient
noncomputable section

/-- The binary column action of the literal covering extension 3.M₂₂.2. -/
def binaryAction : Representation (ZMod 2) actionGroup M22TripleCover.BinarySpace :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    ((Units.coeHom Matrix12).comp actionGroup.subtype)

/-- The full matrix normalizer of the triple cover is contained in its
specified covering extension, using perfectness and quotient coverage. -/

theorem derived_normalizer_le_actionGroup :
    normalizer (derivedGroup : Set Matrix12ˣ) ≤ actionGroup := by
  intro g hg
  let n : normalizer (derivedGroup : Set Matrix12ˣ) := ⟨g, hg⟩
  obtain ⟨a, ha⟩ := derivedQuotientConjugation_surjective
    (Subgroup.quotientAut (center derivedGroup) (derivedGroup.normalizerMonoidHom n))
  have he : derivedConjugation a = derivedGroup.normalizerMonoidHom n :=
    MulAut.quotient_center_injective ha
  have hk : (toDerivedNormalizer a)⁻¹ * n ∈ derivedGroup.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (derivedConjugation a)⁻¹ * derivedGroup.normalizerMonoidHom n = 1
    rw [he, inv_mul_cancel]
  rw [Subgroup.normalizerMonoidHom_ker] at hk
  have hc : (a : Matrix12ˣ)⁻¹ * g ∈ actionGroup := centralizer_derivedGroup_le hk
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using actionGroup.mul_mem a.property hc

private theorem cover_conj_scalar (d : M22TripleCover) :
    coverInclusion d * scalarElement * (coverInclusion d)⁻¹ = scalarElement := by
  change coverInclusion d * coverInclusion M22TripleCover.scalar *
    (coverInclusion d)⁻¹ = coverInclusion M22TripleCover.scalar
  have hd : d * M22TripleCover.scalar * d⁻¹ = M22TripleCover.scalar := by
    rw [mem_center_iff.mp M22TripleCover.scalar_mem_center d,
      mul_assoc, mul_inv_cancel, mul_one]
  exact congrArg coverInclusion hd

/-- Every matrix outside the cover inverts its marked central scalar. -/
theorem triple_outer_conj_scalar (g : actionGroup) (hg : g ∉ coverSubgroup) :
    g * scalarElement * g⁻¹ = scalarElement⁻¹ := by
  have hm : g * outerElement ∈ coverSubgroup :=
    (Subgroup.mul_mem_iff_of_index_two coverSubgroup_index).mpr
      (iff_of_false hg outerElement_not_mem_cover)
  rw [← coverInclusion_range] at hm
  obtain ⟨d, hd⟩ := hm
  have he : g = coverInclusion d * outerElement := by
    rw [hd, mul_assoc, ← pow_two, outerElement_sq, mul_one]
  rw [he, mul_inv_rev]
  calc
    coverInclusion d * outerElement * scalarElement *
        (outerElement⁻¹ * (coverInclusion d)⁻¹) =
      coverInclusion d * (outerElement * scalarElement * outerElement⁻¹) *
        (coverInclusion d)⁻¹ := by simp only [mul_assoc]
    _ = coverInclusion d * scalarElement⁻¹ * (coverInclusion d)⁻¹ := by
      rw [outerElement_conj_scalar]
    _ = scalarElement⁻¹ := by
      change (MulAut.conj (coverInclusion d)) scalarElement⁻¹ = scalarElement⁻¹
      rw [map_inv]
      exact congrArg Inv.inv (cover_conj_scalar d)

open Representation.SL2FourNatural

/-- The actual ambient binary action in the fixed six-dimensional F₄ coordinates. -/
def tripleFieldAction : Representation (ZMod 2) actionGroup M22TripleCover.Unitary.Vector :=
  M22TripleCover.Unitary.binaryCoordinates.conjRingEquiv.toMonoidHom.comp
    binaryAction

theorem tripleFieldAction_on_component (g : M22TripleCover) (v : M22TripleCover.Unitary.Vector) :
    tripleFieldAction (coverInclusion g) v = M22TripleCover.Unitary.fieldAction g v := rfl

theorem tripleFieldAction_scalar (v : M22TripleCover.Unitary.Vector) :
    tripleFieldAction scalarElement v = (QuadraticAlgebra.omega : F) • v := by
  change M22TripleCover.Unitary.coordinateMap
    (M22TripleCover.binaryRepresentation M22TripleCover.scalar
      (M22TripleCover.Unitary.binaryCoordinates.symm v)) = _
  rw [M22TripleCover.Unitary.coordinateMap_scalar]
  exact congrArg (fun w => (QuadraticAlgebra.omega : F) • w)
    (M22TripleCover.Unitary.binaryCoordinates.apply_symm_apply v)

/-- Every outer matrix is semilinear for the nontrivial F₄ automorphism. -/
theorem tripleFieldAction_outer_semilinear (g : actionGroup) (hg : g ∉ coverSubgroup)
    (a : F) (v : M22TripleCover.Unitary.Vector) :
    tripleFieldAction g (a • v) = fieldFrobenius a • tripleFieldAction g v := by
  have hs : scalarElement⁻¹ = scalarElement ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']
    simpa only [scalarElement_order] using pow_orderOf_eq_one scalarElement
  have hgs : g * scalarElement = scalarElement ^ 2 * g := by
    have he := triple_outer_conj_scalar g hg
    rw [hs] at he
    have hh := congrArg (fun x => x * g) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  have hw (w : M22TripleCover.Unitary.Vector) :
      tripleFieldAction g ((QuadraticAlgebra.omega : F) • w) =
        fieldFrobenius (QuadraticAlgebra.omega : F) • tripleFieldAction g w := by
    rw [← tripleFieldAction_scalar]
    change (tripleFieldAction g * tripleFieldAction scalarElement) w = _
    rw [← map_mul, hgs, map_mul, map_pow]
    change tripleFieldAction scalarElement (tripleFieldAction scalarElement
      (tripleFieldAction g w)) = _
    rw [tripleFieldAction_scalar, tripleFieldAction_scalar,
      ← mul_smul, fieldFrobenius_apply, pow_two]
  have ha : a = 0 ∨ a = 1 ∨ a = QuadraticAlgebra.omega ∨
      a = 1 + QuadraticAlgebra.omega := by
    revert a
    decide +kernel
  rcases ha with rfl | rfl | rfl | rfl
  · simp only [zero_smul, map_zero]
  · simp only [one_smul, map_one]
  · exact hw v
  · simp only [add_smul, one_smul, map_add, hw, map_one]

/-- Every matrix in the cover is F₄-linear. -/
theorem tripleFieldAction_inner_linear (g : actionGroup) (hg : g ∈ coverSubgroup)
    (a : F) (v : M22TripleCover.Unitary.Vector) :
    tripleFieldAction g (a • v) = a • tripleFieldAction g v := by
  rw [← coverInclusion_range] at hg
  obtain ⟨d, rfl⟩ := hg
  exact (M22TripleCover.Unitary.fieldAction d).map_smul a v

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  (e : L ≃* M22TripleCover)
  (E : Equiv (ρ.comp L.subtype) (M22TripleCover.representationOfEquiv e))

/-- Transport the given ambient representation through its chosen component intertwiner. -/
def markedTripleMatrixHom : G →* Matrix12ˣ :=
  Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp
    (Representation.asGroupHom (E.toLinearEquiv.conjRingEquiv.toMonoidHom.comp ρ))

theorem markedTripleMatrixHom_apply (g : G) (v : V) :
    (markedTripleMatrixHom ρ L e E g : Matrix12) *ᵥ E v = E (ρ g v) := by
  change LinearMap.toMatrix' (E.toLinearEquiv.conjRingEquiv (ρ g)) *ᵥ E v = _
  rw [LinearMap.toMatrix'_mulVec]
  change E (ρ g (E.symm (E v))) = _
  rw [E.symm_apply_apply]

theorem markedTripleMatrixHom_on_component (x : L) :
    markedTripleMatrixHom ρ L e E x = (e x : Matrix12ˣ) := by
  apply Units.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨w, rfl⟩ := E.surjective v
  change (markedTripleMatrixHom ρ L e E x : Matrix12) *ᵥ E w = _
  rw [markedTripleMatrixHom_apply]
  exact LinearMap.congr_fun (E.isIntertwining' x) w

theorem markedTripleMatrixHom_component_image :
    L.map (markedTripleMatrixHom ρ L e E) = derivedGroup := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [markedTripleMatrixHom_on_component ρ L e E ⟨y, hy⟩] using (e ⟨y, hy⟩).property
  · intro hx
    obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
    exact ⟨y, y.property, (markedTripleMatrixHom_on_component ρ L e E y).trans
      (congrArg Subtype.val hy)⟩

/-- The same transported action factors through the literal covering extension. -/
def markedTripleAmbientHom [L.Normal] : G →* actionGroup :=
  (markedTripleMatrixHom ρ L e E).codRestrict actionGroup (fun g => by
    apply derived_normalizer_le_actionGroup
    rw [← markedTripleMatrixHom_component_image ρ L e E]
    exact L.le_normalizer_map (markedTripleMatrixHom ρ L e E)
      ⟨g, le_normalizer_of_normal (mem_top g), rfl⟩)

theorem markedTripleAmbientHom_on_component [L.Normal] (x : L) :
    markedTripleAmbientHom ρ L e E x = coverInclusion (e x) :=
  Subtype.ext (markedTripleMatrixHom_on_component ρ L e E x)

theorem markedTripleAmbientHom_intertwining [L.Normal] (g : G) (v : V) :
    E (ρ g v) = binaryAction
      (markedTripleAmbientHom ρ L e E g) (E v) :=
  (markedTripleMatrixHom_apply ρ L e E g v).symm

theorem markedTripleAmbientHom_injective [L.Normal] (hf : Function.Injective ρ) :
    Function.Injective (markedTripleAmbientHom ρ L e E) := by
  intro x y hxy
  apply hf
  apply LinearMap.ext
  intro v
  apply E.injective
  change E (ρ x v) = E (ρ y v)
  rw [markedTripleAmbientHom_intertwining ρ L e E,
    markedTripleAmbientHom_intertwining ρ L e E, hxy]

theorem markedTripleAmbientHom_image [L.Normal] :
    L.map (markedTripleAmbientHom ρ L e E) = coverSubgroup := by
  rw [← coverInclusion_range]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨e ⟨y, hy⟩, (markedTripleAmbientHom_on_component ρ L e E ⟨y, hy⟩).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := e.surjective y
    exact ⟨z, z.property, markedTripleAmbientHom_on_component ρ L e E z⟩

/-- An ambient action containing the cover has inner or full matrix image. -/
theorem markedTripleAmbientHom_range_cases [L.Normal] :
    (markedTripleAmbientHom ρ L e E).range = coverSubgroup ∨
      (markedTripleAmbientHom ρ L e E).range = ⊤ := by
  let R := (markedTripleAmbientHom ρ L e E).range
  have hle : coverSubgroup ≤ R := by
    rw [← markedTripleAmbientHom_image ρ L e E]
    exact Subgroup.map_le_range (f := markedTripleAmbientHom ρ L e E) L
  by_cases he : R = coverSubgroup
  · exact Or.inl he
  right
  apply top_unique
  have hn : ¬ R ≤ coverSubgroup := fun h => he (le_antisymm h hle)
  obtain ⟨a, haR, ha⟩ := SetLike.not_le_iff_exists.mp hn
  intro x _
  by_cases hx : x ∈ coverSubgroup
  · exact hle hx
  have hxa : x * a⁻¹ ∈ coverSubgroup :=
    (Subgroup.mul_mem_iff_of_index_two coverSubgroup_index).mpr
      (iff_of_false hx (fun h => ha (coverSubgroup.inv_mem h)))
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using R.mul_mem (hle hxa) haR

theorem markedTripleAmbientHom_mem_cover_iff [L.Normal] (hf : Function.Injective ρ) (g : G) :
    markedTripleAmbientHom ρ L e E g ∈ coverSubgroup ↔ g ∈ L := by
  rw [← markedTripleAmbientHom_image ρ L e E]
  exact Subgroup.mem_map_iff_mem (markedTripleAmbientHom_injective ρ L e E hf)

end
end Sporadic.Mathieu.M22TripleCover.Ambient
