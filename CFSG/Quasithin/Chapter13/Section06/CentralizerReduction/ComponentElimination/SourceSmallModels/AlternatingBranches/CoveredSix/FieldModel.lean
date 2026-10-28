module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.FieldModel.CubicNorm
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage

/-!
# Field structure and actual hexacode coordinates for covered-six blocks

The exceptional-block predicate supplies a faithful action on the original
six-dimensional binary U. The central cubic norm vanishes by the block's
irreducibility interval and [U,K]=U, so evaluation of F₄ at the central
operator makes U three-dimensional over F₄. Every original conjugation
operator is field-linear. The proved finite even-image recognition then
constructs actual linear coordinates and a quotient-group isomorphism.

`exists_coordinates_over_projection` retains the prescribed covering map
and displays the actor automorphism twist separately. `exists_field_model`
and `nonempty_hexacodeModel` require only the exceptional-block predicate.
The original action, covering comparison and umbrella modules are preserved.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.22,
printed p.129 (the covered-six definition), K.1.3, printed p.453, and
13.6.22, printed p.932. The finite recognition and its licensed ATLAS
model are reused through `HexacodeAction.SixDimensionalRecognition.EvenImage`.
-/

public section

open Subgroup CFSG.Quasithin.ChapterC Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
variable {K : Type*} [Group K] (h : IsExceptionalAhat6Block K)
variable [IsElementaryAbelian 2 (blockU K)]

open Atlas.Codes Representation.Hexacode Representation.Hexacode.SixDimensional

/-- The cubic actor on U selected by an actual even-cover isomorphism. -/
@[expose] def cubicActor (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) : K ⧸ pCore 2 K :=
  f.symm hexEvenZ

omit [IsElementaryAbelian 2 (blockU K)] in
private theorem cubicActor_central (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) :
    cubicActor f ∈ center (K ⧸ pCore 2 K) := by
  rw [mem_center_iff]
  intro g
  apply f.injective
  simp only [map_mul, cubicActor, f.apply_symm_apply]
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.mp (hex_conjugation_even (f g).val (f g).property)

omit [IsElementaryAbelian 2 (blockU K)] in
private theorem cubicActor_ne_one (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) :
    cubicActor f ≠ 1 := by
  intro he
  have hh := congrArg (fun x => (f x).val) he
  apply hexZ_ne_one
  simpa only [cubicActor, f.apply_symm_apply, map_one, Subgroup.coe_one, hexEvenZ] using hh

omit [IsElementaryAbelian 2 (blockU K)] in
private theorem cubicActor_cube (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) :
    cubicActor f ^ 3 = 1 := by
  apply f.injective
  simp only [map_pow, cubicActor, f.apply_symm_apply, map_one]
  exact Subtype.ext hexZ_cube

/-- The primitive cubic actor satisfies the field polynomial on the original U. -/
theorem cubicActor_quadratic (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) :
    binaryAction h (cubicActor f) ^ 2 + binaryAction h (cubicActor f) + 1 = 0 :=
  central_cubic_quadratic h _ (cubicActor_central f) (cubicActor_ne_one f) (cubicActor_cube f)

/-- Evaluate F₄ at the selected central cubic operator. -/
@[expose] noncomputable def fieldScalarMap (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) :
    F →ₐ[Bit] Module.End Bit (Additive (blockU K)) :=
  QuadraticAlgebra.lift ⟨binaryAction h (cubicActor f), by
    have he : binaryAction h (cubicActor f) ^ 2 = -(binaryAction h (cubicActor f) + 1) := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [add_assoc] using cubicActor_quadratic h f
    have hn (a : Module.End Bit (Additive (blockU K))) : -a = a := by
      rw [← neg_one_smul Bit, show (-1 : Bit) = 1 by decide, one_smul]
    simpa only [pow_two, hn, one_smul, add_comm] using he⟩

/-- The recovered F₄-module structure is on the original additive group U. -/
@[expose, instance_reducible] noncomputable def fieldModule
    (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) : Module F (Additive (blockU K)) :=
  Module.compHom _ (fieldScalarMap h f).toRingHom

/-- The recovered scalars extend the specified binary scalars. -/
theorem fieldTower (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) :
    letI := fieldModule h f
    IsScalarTower Bit F (Additive (blockU K)) := by
  let := fieldModule h f
  constructor
  intro r a v
  change fieldScalarMap h f (r • a) v = r • (fieldScalarMap h f a v)
  rw [map_smul]
  rfl

/-- Scalar multiplication retains the actual central cubic action. -/
theorem field_smul_formula (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms)
    (a : F) (v : Additive (blockU K)) : letI := fieldModule h f
    a • v = a.re • v + a.im • binaryAction h (cubicActor f) v := rfl

/-- The selected cubic generator acts as the primitive scalar. -/
theorem field_cubic_scalar (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms)
    (v : Additive (blockU K)) : letI := fieldModule h f
    binaryAction h (cubicActor f) v = omega • v := by
  change binaryAction h (cubicActor f) v =
    (0 : Bit) • v + (1 : Bit) • binaryAction h (cubicActor f) v
  simp only [zero_smul, one_smul, zero_add]

/-- The literal quotient action is linear over the recovered field. -/
noncomputable def fieldRepresentation (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) :
    letI := fieldModule h f
    Representation F (K ⧸ pCore 2 K) (Additive (blockU K)) := by
  let := fieldModule h f
  refine { toFun := fun g => { (binaryAction h g).toAddHom with map_smul' := ?_ }
           map_one' := ?_, map_mul' := ?_ }
  · intro a v
    have hc : binaryAction h g (binaryAction h (cubicActor f) v) =
        binaryAction h (cubicActor f) (binaryAction h g v) := by
      change (binaryAction h g * binaryAction h (cubicActor f)) v =
        (binaryAction h (cubicActor f) * binaryAction h g) v
      rw [← map_mul, ← map_mul, mem_center_iff.mp (cubicActor_central f) g]
    change binaryAction h g (a.re • v + a.im • binaryAction h (cubicActor f) v) =
      a.re • binaryAction h g v + a.im • binaryAction h (cubicActor f) (binaryAction h g v)
    rw [map_add, map_smul, map_smul, hc]
  · apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (binaryAction h).map_one v
  · intro g j
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun ((binaryAction h).map_mul g j) v

/-- Recovering the field leaves every original operator unchanged. -/
theorem fieldRepresentation_apply (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms)
    (g : K ⧸ pCore 2 K) (v : Additive (blockU K)) :
    fieldRepresentation h f g v = binaryAction h g v := by rfl

/-- The recovered field action is still literal conjugation by representatives. -/
theorem fieldRepresentation_conjugation (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms)
    (k : K) (v : Additive (blockU K)) :
    ((fieldRepresentation h f (QuotientGroup.mk' (pCore 2 K) k) v).toMul : K) =
      k * (v.toMul : K) * k⁻¹ := binaryAction_apply h k v

/-- The original U has field dimension three. -/
theorem field_finrank (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) :
    letI := fieldModule h f
    Module.finrank F (Additive (blockU K)) = 3 := by
  let := fieldModule h f
  let := fieldTower h f
  have hd := Module.finrank_mul_finrank Bit F (Additive (blockU K))
  rw [QuadraticAlgebra.finrank_eq_two, binary_finrank h] at hd
  omega

/-- Faithfulness of the original action persists over F₄. -/
theorem fieldRepresentation_injective (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) :
    letI := fieldModule h f
    Function.Injective (fieldRepresentation h f) := by
  let := fieldModule h f
  intro g j he
  apply binaryAction_injective h
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun he v

/-- Recognition keeps its actor automorphism explicit. The field coordinates
intertwine every original actor and vector after precisely this twist. -/
theorem exists_field_coordinates (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) :
    letI := fieldModule h f
    ∃ (b : MulAut HexEvenAutomorphisms) (c : Additive (blockU K) ≃ₗ[F] hexacode),
      ∀ g v, c (fieldRepresentation h f g v) = evenFieldAction (b (f g)) (c v) := by
  let := h.1.finite
  let := fieldModule h f
  let := fieldTower h f
  let E : Additive (blockU K) ≃ₗ[F] hexacode :=
    LinearEquiv.ofFinrankEq _ _ ((field_finrank h f).trans Hexacode.field_finrank.symm)
  let ρ := (fieldRepresentation h f).comp f.symm.toMonoidHom
  have hf : Function.Injective ρ := (fieldRepresentation_injective h f).comp f.symm.injective
  obtain ⟨b, d, hd⟩ := EvenImage.exists_twist (coordinateAction ρ E)
    (coordinateAction_injective ρ E hf)
  refine ⟨b, E.trans d, ?_⟩
  intro g v
  have he := hd (f g) (E v)
  change d (E (fieldRepresentation h f (f.symm (f g)) (E.symm (E v)))) =
    evenFieldAction (b (f g)) (d (E v)) at he
  simpa only [LinearEquiv.trans_apply, E.symm_apply_apply, f.symm_apply_apply] using he

/-- Binary coordinates for any prescribed cover isomorphism retain the explicit twist. -/
theorem exists_binary_coordinates (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) :
    ∃ (b : MulAut HexEvenAutomorphisms) (c : Additive (blockU K) ≃ₗ[Bit] hexacode),
      ∀ g v, c (binaryAction h g v) = Hexacode.action (b (f g)).val (c v) := by
  let := fieldModule h f
  let := fieldTower h f
  obtain ⟨b, c, hc⟩ := exists_field_coordinates h f
  exact ⟨b, c.restrictScalars Bit, hc⟩

/-- Coordinates over a prescribed central quotient map, with the necessary
actor twist recorded separately from the projection-preserving cover comparison. -/
theorem exists_coordinates_over_projection
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* alternatingGroup (Fin 6)) :
    ∃ (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms)
      (b : MulAut HexEvenAutomorphisms) (c : Additive (blockU K) ≃ₗ[Bit] hexacode),
      hexEvenCoordinate.comp f.toMonoidHom =
        e.toMonoidHom.comp (QuotientGroup.mk' (center (K ⧸ pCore 2 K))) ∧
      ∀ g v, c (binaryAction h g v) = Hexacode.action (b (f g)).val (c v) := by
  obtain ⟨f, hf⟩ := exists_cover_equiv h e
  obtain ⟨b, c, hc⟩ := exists_binary_coordinates h f
  exact ⟨f, b, c, hf, hc⟩

omit [IsElementaryAbelian 2 (blockU K)] in
/-- The block hypothesis alone supplies compatible field scalars, dimension three,
and a faithful field-linear action with actual hexacode coordinates. -/
theorem exists_field_model : letI := h.1.elementary
    ∃ m : Module F (Additive (blockU K)), letI := m
      IsScalarTower Bit F (Additive (blockU K)) ∧
      Module.finrank F (Additive (blockU K)) = 3 ∧
      ∃ (ρ : Representation F (K ⧸ pCore 2 K) (Additive (blockU K)))
        (f : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms)
        (c : Additive (blockU K) ≃ₗ[F] hexacode),
        Function.Injective ρ ∧ (∀ g v, ρ g v = binaryAction h g v) ∧
        (∀ (k : K) v, ((ρ (QuotientGroup.mk' (pCore 2 K) k) v).toMul : K) =
          k * (v.toMul : K) * k⁻¹) ∧
        ∀ g v, c (ρ g v) = evenFieldAction (f g) (c v) := by
  let := h.1.elementary
  obtain ⟨e⟩ := h.2.2.2.1
  obtain ⟨f, _⟩ := exists_cover_equiv h e
  let := fieldModule h f
  obtain ⟨b, c, hc⟩ := exists_field_coordinates h f
  exact ⟨fieldModule h f, fieldTower h f, field_finrank h f,
    fieldRepresentation h f, f.trans b, c, fieldRepresentation_injective h f,
    fieldRepresentation_apply h f, fieldRepresentation_conjugation h f, hc⟩

omit [IsElementaryAbelian 2 (blockU K)] in
/-- The exceptional-block predicate alone supplies the actual hexacode model. -/
theorem nonempty_hexacodeModel : letI := h.1.elementary
    Nonempty (HexacodeModel h) := by
  let := h.1.elementary
  obtain ⟨e⟩ := h.2.2.2.1
  obtain ⟨f, b, c, _, hc⟩ := exists_coordinates_over_projection h e
  exact ⟨{ quotientIso := f.trans b, coordinates := c, intertwining := hc }⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
