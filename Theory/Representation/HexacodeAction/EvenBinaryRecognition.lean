module
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage
public import Theory.Representation.HexacodeAction.Cover

/-!
# Recognition of irreducible binary six-dimensional even hexacode actions

The nontrivial central cubic acts fixed-point freely by Schur's lemma.
Its quadratic equation recovers the four-element field on the original
module. The faithful field-linear three-dimensional action is then recognized
by the existing finite even-image theorem. Both the actor twist and vector
coordinates are retained; no extension to an odd automorphism is assumed.

Source: Aschbacher--Smith K.1.3, printed p.453, and the covered-six action in
13.6.22, p.932. The concrete code and finite recognition retain their ATLAS
attribution through the imported modules.
-/

public section
open Atlas.Codes Subgroup
namespace Representation.Hexacode.EvenBinaryRecognition
open SixDimensional
variable {W : Type*} [AddCommGroup W] [Module Bit W]
  (ρ : Representation Bit HexEvenAutomorphisms W)

private theorem scalar_central : hexEvenZ ∈ center HexEvenAutomorphisms := by
  rw [← even_kernel_eq_center, hexEvenCoordinate_kernel]
  exact mem_zpowers _

private theorem scalar_commutes (g : HexEvenAutomorphisms) (w : W) :
    ρ hexEvenZ (ρ g w) = ρ g (ρ hexEvenZ w) := by
  have h := mem_center_iff.mp scalar_central g
  simpa only [map_mul, Module.End.mul_apply] using
    congrArg (fun x => ρ x w) h.symm

private theorem scalar_fixed_iff (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ) (w : W) : ρ hexEvenZ w = w ↔ w = 0 := by
  let := hi
  let f : IntertwiningMap ρ ρ :=
    { toLinearMap := ρ hexEvenZ - 1
      isIntertwining' := by
        intro g
        ext v
        change ρ hexEvenZ (ρ g v) - ρ g v = ρ g (ρ hexEvenZ v - v)
        rw [map_sub, scalar_commutes] }
  have hfn : f ≠ 0 := by
    intro h
    apply hexZ_ne_one
    have hz : hexEvenZ = 1 := by
      apply hf
      ext v
      have he := congrArg (fun f : IntertwiningMap ρ ρ => f v) h
      exact (sub_eq_zero.mp he).trans (by simp)
    exact congrArg Subtype.val hz
  have hfi : Function.Injective f := (IsIrreducible.injective_or_eq_zero f).resolve_right hfn
  constructor
  · intro h
    apply hfi
    change ρ hexEvenZ w - w = ρ hexEvenZ 0 - 0
    simp only [h, map_zero, sub_self]
  · rintro rfl
    exact map_zero _

private theorem scalar_quadratic (hf : Function.Injective ρ) (hi : IsIrreducible ρ) :
    ρ hexEvenZ ^ 2 + ρ hexEvenZ + 1 = 0 := by
  have hc (w : W) : ρ hexEvenZ (ρ hexEvenZ (ρ hexEvenZ w)) = w := by
    have hp : ρ hexEvenZ ^ 3 = 1 := by
      rw [← map_pow, show hexEvenZ ^ 3 = 1 from Subtype.ext hexZ_cube, map_one]
    simpa only [pow_succ, pow_zero, one_mul, Module.End.mul_apply,
      Module.End.one_apply] using LinearMap.congr_fun hp w
  ext w
  apply (scalar_fixed_iff ρ hf hi _).mp
  change ρ hexEvenZ (ρ hexEvenZ (ρ hexEvenZ w) + ρ hexEvenZ w + w) =
    ρ hexEvenZ (ρ hexEvenZ w) + ρ hexEvenZ w + w
  rw [map_add, map_add, hc]
  abel

variable (hq : ρ hexEvenZ ^ 2 + ρ hexEvenZ + 1 = 0)

private noncomputable def scalarMap : F →ₐ[Bit] Module.End Bit W :=
  QuadraticAlgebra.lift ⟨ρ hexEvenZ, by
    have he : ρ hexEvenZ ^ 2 = -(ρ hexEvenZ + 1) := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [add_assoc] using hq
    have hn (f : Module.End Bit W) : -f = f := by
      rw [← neg_one_smul Bit, show (-1 : Bit) = 1 by decide, one_smul]
    simpa only [pow_two, hn, one_smul, add_comm] using he⟩

@[instance_reducible] private noncomputable def fieldModule : Module F W :=
  Module.compHom W (scalarMap ρ hq).toRingHom

private theorem fieldTower : letI := fieldModule ρ hq
    IsScalarTower Bit F W := by
  let := fieldModule ρ hq
  constructor
  intro r a v
  change scalarMap ρ hq (r • a) v = r • (scalarMap ρ hq a v)
  rw [map_smul]
  rfl

private noncomputable def fieldRepresentation : letI := fieldModule ρ hq
    Representation F HexEvenAutomorphisms W := by
  let := fieldModule ρ hq
  refine { toFun := fun g => { (ρ g).toAddHom with map_smul' := ?_ }
           map_one' := ?_, map_mul' := ?_ }
  · intro a v
    change ρ g (a.re • v + a.im • ρ hexEvenZ v) =
      a.re • ρ g v + a.im • ρ hexEvenZ (ρ g v)
    rw [map_add, map_smul, map_smul, scalar_commutes]
  · ext v
    exact LinearMap.congr_fun ρ.map_one v
  · intro g h
    ext v
    exact LinearMap.congr_fun (ρ.map_mul g h) v

/-- Every faithful irreducible binary six-dimensional action of the actual
cover has hexacode coordinates, with its necessary actor twist explicit. -/
theorem exists_equivariant [Module.Finite Bit W]
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (hd : Module.finrank Bit W = 6) :
    ∃ (a : MulAut HexEvenAutomorphisms) (e : W ≃ₗ[Bit] hexacode),
      ∀ g w, e (ρ g w) = evenAction (a g) (e w) := by
  have hq := scalar_quadratic ρ hf hi
  let := fieldModule ρ hq
  let := fieldTower ρ hq
  let : Module.Finite F W := Module.Finite.of_restrictScalars_finite Bit F W
  have hdim : Module.finrank F W = 3 := by
    have he := Module.finrank_mul_finrank Bit F W
    rw [QuadraticAlgebra.finrank_eq_two, hd] at he
    omega
  let E : W ≃ₗ[F] hexacode :=
    LinearEquiv.ofFinrankEq _ _ (hdim.trans Hexacode.field_finrank.symm)
  have hfaith : Function.Injective (fieldRepresentation ρ hq) := by
    intro g h he
    apply hf
    ext v
    exact LinearMap.congr_fun he v
  obtain ⟨a, c, hc⟩ := EvenImage.exists_twist (coordinateAction (fieldRepresentation ρ hq) E)
    (coordinateAction_injective _ E hfaith)
  refine ⟨a, (E.trans c).restrictScalars Bit, ?_⟩
  intro g w
  have h := hc g (E w)
  change c (E (ρ g (E.symm (E w)))) = evenAction (a g) (c (E w)) at h
  simpa only [LinearEquiv.restrictScalars_apply, LinearEquiv.trans_apply,
    E.symm_apply_apply] using h

end Representation.Hexacode.EvenBinaryRecognition
