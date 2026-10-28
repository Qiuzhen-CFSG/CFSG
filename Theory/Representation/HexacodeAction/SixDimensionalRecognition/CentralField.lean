module

public import Theory.Representation.HexacodeAction.TerminalIrreducible

/-!
# Recovering the central field on a binary hexacode-group module

On a faithful module irreducible for the even cover, the displacement of
`hexZ` is a nonzero intertwiner. Schur's lemma makes it injective. The
order-three relation then gives `z² + z + 1 = 0`, and evaluation of the
quadratic field at this operator equips the original additive group with
F₄ scalars. Even elements are field-linear; odd elements invert `hexZ`
and are semilinear for Frobenius. The binary six-space has field dimension
three, and perfectness gives determinant one.

These are intrinsic reductions for the representation recognition in
Aschbacher–Smith, *The Classification of Quasithin Groups*, K.1.3,
printed p.453 (PDF p.464), used on printed p.1155 (PDF p.1172).
They do not classify embeddings of the even group in SL₃(4).
The quadratic-field construction follows the existing generic calculation
in `SL3FourLocalCatalogue.CentralReduction`, specialized here without its
SL₃(4) representation hypotheses or imports. The concrete group and its
relations come from the licensed ATLAS imports of `HexacodeAction.Field`.
-/

@[expose] public section

open Atlas.Codes
namespace Representation.Hexacode.SixDimensional

variable {W : Type*} [AddCommGroup W] [Module Bit W]
    (ρ : Representation Bit HexAutomorphisms W)

/-- The central cubic operator commutes with every even operator. -/
theorem scalar_commutes (g : HexEvenAutomorphisms) (w : W) :
    ρ hexZ (ρ g.val w) = ρ g.val (ρ hexZ w) := by
  have h := mul_inv_eq_iff_eq_mul.mp (hex_conjugation_even g.val g.property)
  have he := congrArg (fun x => ρ x w) h
  simpa only [map_mul, Module.End.mul_apply] using he.symm

/-- Faithfulness and even irreducibility make the cubic operator fixed-point free. -/
theorem scalar_fixed_iff (hf : Function.Injective ρ)
    (hi : IsIrreducible (ρ.comp hexSign.ker.subtype)) (w : W) :
    ρ hexZ w = w ↔ w = 0 := by
  let := hi
  let σ := ρ.comp hexSign.ker.subtype
  let f : IntertwiningMap σ σ :=
    { toLinearMap := ρ hexZ - 1
      isIntertwining' := by
        intro g
        ext v
        change ρ hexZ (ρ g.val v) - ρ g.val v = ρ g.val (ρ hexZ v - v)
        rw [map_sub, scalar_commutes] }
  have hfn : f ≠ 0 := by
    intro h
    apply hexZ_ne_one
    apply hf
    ext v
    have he := congrArg (fun f : IntertwiningMap σ σ => f v) h
    exact (sub_eq_zero.mp he).trans (by simp)
  have hfi : Function.Injective f := (IsIrreducible.injective_or_eq_zero f).resolve_right hfn
  constructor
  · intro h
    apply hfi
    change ρ hexZ w - w = ρ hexZ 0 - 0
    simp only [h, map_zero, sub_self]
  · rintro rfl
    exact map_zero _

/-- The nontrivial central character satisfies the quadratic field relation. -/
theorem scalar_quadratic (hf : Function.Injective ρ)
    (hi : IsIrreducible (ρ.comp hexSign.ker.subtype)) :
    ρ hexZ ^ 2 + ρ hexZ + 1 = 0 := by
  have hc (w : W) : ρ hexZ (ρ hexZ (ρ hexZ w)) = w := by
    have hp : ρ hexZ ^ 3 = 1 := by rw [← map_pow, hexZ_cube, map_one]
    simpa only [pow_succ, pow_zero, one_mul, Module.End.mul_apply,
      Module.End.one_apply] using LinearMap.congr_fun hp w
  ext w
  apply (scalar_fixed_iff ρ hf hi _).mp
  change ρ hexZ (ρ hexZ (ρ hexZ w) + ρ hexZ w + w) =
    ρ hexZ (ρ hexZ w) + ρ hexZ w + w
  rw [map_add, map_add, hc]
  abel

variable (hq : ρ hexZ ^ 2 + ρ hexZ + 1 = 0)

/-- Evaluate the four-element field at the cubic operator. -/
noncomputable def scalarMap : F →ₐ[Bit] Module.End Bit W :=
  QuadraticAlgebra.lift ⟨ρ hexZ, by
    have he : ρ hexZ ^ 2 = -(ρ hexZ + 1) := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [add_assoc] using hq
    have hn (f : Module.End Bit W) : -f = f := by
      rw [← neg_one_smul Bit, show (-1 : Bit) = 1 by decide, one_smul]
    simpa only [pow_two, hn, one_smul, add_comm] using he⟩

/-- The recovered field scalars on the original additive group. -/
@[instance_reducible] noncomputable def fieldModule : Module F W :=
  Module.compHom W (scalarMap ρ hq).toRingHom

/-- The recovered field action extends the original binary scalars. -/
theorem fieldTower : letI := fieldModule ρ hq
    IsScalarTower Bit F W := by
  let := fieldModule ρ hq
  constructor
  intro r a v
  change scalarMap ρ hq (r • a) v = r • (scalarMap ρ hq a v)
  rw [map_smul]
  rfl

/-- Field scalars are binary combinations of identity and the cubic operator. -/
theorem field_smul_formula (a : F) (w : W) : letI := fieldModule ρ hq
    a • w = a.re • w + a.im • ρ hexZ w := rfl

/-- The marked central element acts as the marked primitive field scalar. -/
theorem field_scalar (w : W) : letI := fieldModule ρ hq
    ρ hexZ w = omega • w := by
  change ρ hexZ w = (0 : Bit) • w + (1 : Bit) • ρ hexZ w
  simp only [zero_smul, one_smul, zero_add]

include hq in
/-- The quadratic relation, evaluated on an actual vector. -/
theorem scalar_square_apply (w : W) : ρ hexZ (ρ hexZ w) = ρ hexZ w + w := by
  have he := LinearMap.congr_fun hq w
  change ρ hexZ (ρ hexZ w) + ρ hexZ w + w = 0 at he
  have hn (v : W) : -v = v := by
    rw [← neg_one_smul Bit, show (-1 : Bit) = 1 by decide, one_smul]
  simpa only [hn] using eq_neg_of_add_eq_zero_left ((add_assoc _ _ _).symm.trans he)

/-- Every odd element is semilinear for the nontrivial field automorphism. -/
theorem odd_smul (g : HexAutomorphisms) (hg : hexSign g = -1) (a : F) (w : W) :
    letI := fieldModule ρ hq
    ρ g (a • w) = SL2FourNatural.fieldFrobenius a • ρ g w := by
  let := fieldModule ρ hq
  have hz : hexZ⁻¹ = hexZ ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']
    exact hexZ_cube
  have hgZ : g * hexZ = hexZ ^ 2 * g := by
    rw [← hz]
    exact mul_inv_eq_iff_eq_mul.mp (hex_conjugation_odd g hg)
  have hc : ρ g (ρ hexZ w) = ρ hexZ (ρ hexZ (ρ g w)) := by
    have he := congrArg (fun x => ρ x w) hgZ
    simpa only [map_mul, map_pow, pow_two, Module.End.mul_apply] using he
  have ha : (SL2FourNatural.fieldFrobenius a).re = a.re + a.im ∧
      (SL2FourNatural.fieldFrobenius a).im = a.im :=
    (by decide : ∀ a : F, (SL2FourNatural.fieldFrobenius a).re = a.re + a.im ∧
      (SL2FourNatural.fieldFrobenius a).im = a.im) a
  rw [field_smul_formula, map_add, map_smul, map_smul, hc, scalar_square_apply ρ hq,
    field_smul_formula, ha.1, ha.2, add_smul, smul_add]
  abel

/-- The actual even action over the recovered four-element field. -/
noncomputable def evenRepresentation : letI := fieldModule ρ hq
    Representation F HexEvenAutomorphisms W := by
  let := fieldModule ρ hq
  refine { toFun := fun g => { (ρ g.val).toAddHom with map_smul' := ?_ }
           map_one' := ?_, map_mul' := ?_ }
  · intro a w
    change ρ g.val (a.re • w + a.im • ρ hexZ w) =
      a.re • ρ g.val w + a.im • ρ hexZ (ρ g.val w)
    rw [map_add, map_smul, map_smul, scalar_commutes]
  · ext w
    exact LinearMap.congr_fun ρ.map_one w
  · intro g h
    ext w
    exact LinearMap.congr_fun (ρ.map_mul g.val h.val) w

/-- Recovering field scalars preserves every original even operator. -/
theorem evenRepresentation_apply (g : HexEvenAutomorphisms) (w : W) :
    evenRepresentation ρ hq g w = ρ g.val w := rfl

/-- Faithfulness is preserved on the even cover. -/
theorem evenRepresentation_injective (hf : Function.Injective ρ) :
    letI := fieldModule ρ hq
    Function.Injective (evenRepresentation ρ hq) := by
  let := fieldModule ρ hq
  intro g h he
  apply Subtype.ext
  apply hf
  ext w
  exact LinearMap.congr_fun he w

/-- The binary dimension is twice the recovered field dimension. -/
theorem field_finrank : letI := fieldModule ρ hq
    2 * Module.finrank F W = Module.finrank Bit W := by
  let := fieldModule ρ hq
  let := fieldTower ρ hq
  have h := Module.finrank_mul_finrank Bit F W
  rwa [QuadraticAlgebra.finrank_eq_two] at h

/-- A binary six-space is three-dimensional over the recovered field. -/
theorem field_finrank_three (hd : Module.finrank Bit W = 6) :
    let := fieldModule ρ hq
    Module.finrank F W = 3 := by
  let := fieldModule ρ hq
  have h := field_finrank ρ hq
  rw [hd] at h
  omega

/-- Perfectness forces determinant one for the recovered even action. -/
theorem evenRepresentation_det (g : HexEvenAutomorphisms) :
    letI := fieldModule ρ hq
    LinearMap.det (evenRepresentation ρ hq g) = 1 := by
  let := fieldModule ρ hq
  let f : HexEvenAutomorphisms →* Fˣ :=
    MonoidHom.toHomUnits (LinearMap.det.comp (evenRepresentation ρ hq))
  let := even_isPerfect
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have h : (⟨f g, ⟨g, rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg (fun x : f.range => (x.val : F)) h

/-- Binary finite generation implies finite generation over the recovered field. -/
theorem field_finite [Module.Finite Bit W] : letI := fieldModule ρ hq
    Module.Finite F W := by
  let := fieldModule ρ hq
  let := fieldTower ρ hq
  exact Module.Finite.of_restrictScalars_finite Bit F W

/-- Choose field coordinates on the code carrier; these are not yet intertwining. -/
noncomputable def fieldCoordinates [Module.Finite Bit W]
    (hd : Module.finrank Bit W = 6) : letI := fieldModule ρ hq
    W ≃ₗ[F] hexacode := by
  letI := fieldModule ρ hq
  letI := field_finite ρ hq
  exact LinearEquiv.ofFinrankEq W hexacode
    ((field_finrank_three ρ hq hd).trans Hexacode.field_finrank.symm)

end Representation.Hexacode.SixDimensional
