module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Contracts
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage

/-!
# Six-dimensional recognition for the even hexacode cover

The nontrivial central cubic has no fixed vectors on a faithful irreducible
binary module, by Schur's lemma. Its quadratic polynomial recovers F₄ on the
original vector space. In binary dimension six the recovered field dimension
is three, so the proved `EvenImage.exists_twist` classifies its faithful
embedding on the actual hexacode. Restricting the resulting intertwiner back
to binary scalars produces an `ActionEquiv` for the entire even group.

This adapts the central-field recovery in
`Theory.Representation.HexacodeAction.SixDimensionalRecognition.CentralField`
to a representation of the even group alone. It reuses the checked finite
embedding classification and assumes no extension of that representation.
The actual source consumer is `hexacodeAction_of_dimension`.

Source: Aschbacher–Smith, K.1.3, printed p.453 (PDF p.464).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Atlas.Codes
open Representation.Hexacode.SixDimensional
namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource
namespace EvenRecognition
variable {W : Type*} [AddCommGroup W] [Module Bit W]
  (τ : Representation Bit HexEvenAutomorphisms W)
private theorem scalar_commutes (g : HexEvenAutomorphisms) (w : W) :
    τ hexEvenZ (τ g w) = τ g (τ hexEvenZ w) := by
  have hg : g * hexEvenZ = hexEvenZ * g := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mp (hex_conjugation_even g.val g.property)
  exact LinearMap.congr_fun (by rw [← map_mul, ← map_mul, hg] :
    τ hexEvenZ * τ g = τ g * τ hexEvenZ) w
private theorem scalar_quadratic (hf : Function.Injective τ) (hi : IsIrreducible τ) :
    τ hexEvenZ ^ 2 + τ hexEvenZ + 1 = 0 := by
  let := hi
  let f : IntertwiningMap τ τ := {
    toLinearMap := τ hexEvenZ - 1
    isIntertwining' := by
      intro g
      ext w
      change τ hexEvenZ (τ g w) - τ g w = τ g (τ hexEvenZ w - w)
      rw [map_sub, scalar_commutes] }
  have hfn : f ≠ 0 := by
    intro h
    have hz : hexEvenZ ≠ 1 := fun hz => hexZ_ne_one (congrArg Subtype.val hz)
    apply hz
    apply hf
    ext w
    have he := congrArg (fun f : IntertwiningMap τ τ => f w) h
    exact (sub_eq_zero.mp he).trans (by simp)
  have hfi : Function.Injective f := (IsIrreducible.injective_or_eq_zero f).resolve_right hfn
  have hc : τ hexEvenZ ^ 3 = 1 := by
    rw [← map_pow, ← hexEvenZ_order, pow_orderOf_eq_one, map_one]
  ext w
  apply hfi
  change τ hexEvenZ (τ hexEvenZ (τ hexEvenZ w) + τ hexEvenZ w + w) -
    (τ hexEvenZ (τ hexEvenZ w) + τ hexEvenZ w + w) = τ hexEvenZ 0 - 0
  have he := LinearMap.congr_fun hc w
  change τ hexEvenZ (τ hexEvenZ (τ hexEvenZ w)) = w at he
  rw [map_add, map_add, he, map_zero]
  abel

variable (hq : τ hexEvenZ ^ 2 + τ hexEvenZ + 1 = 0)
private noncomputable def scalarMap : Hexacode.F →ₐ[Bit] Module.End Bit W :=
  QuadraticAlgebra.lift ⟨τ hexEvenZ, by
    have he : τ hexEvenZ ^ 2 = -(τ hexEvenZ + 1) := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [add_assoc] using hq
    have hn (f : Module.End Bit W) : -f = f := by
      rw [← neg_one_smul Bit, show (-1 : Bit) = 1 by decide, one_smul]
    simpa only [pow_two, hn, one_smul, add_comm] using he⟩
@[instance_reducible] private noncomputable def fieldModule : Module Hexacode.F W :=
  Module.compHom W (scalarMap τ hq).toRingHom
private theorem fieldTower : let := fieldModule τ hq
    IsScalarTower Bit Hexacode.F W := by
  let := fieldModule τ hq
  constructor
  intro r a v
  change scalarMap τ hq (r • a) v = r • (scalarMap τ hq a v)
  rw [map_smul]
  rfl

/-- The even-cover version of six-dimensional recognition, using the proved
finite F₄ embedding classification on the actual hexacode. -/
theorem exists_actionEquiv [Module.Finite Bit W]
    (hf : Function.Injective τ) (hi : IsIrreducible τ)
    (hd : Module.finrank Bit W = 6) : Nonempty (ActionEquiv τ Hexacode.evenAction) := by
  let hq := scalar_quadratic τ hf hi
  let := fieldModule τ hq
  let := fieldTower τ hq
  let : Module.Finite Hexacode.F W := Module.Finite.of_restrictScalars_finite Bit Hexacode.F W
  have hdF : Module.finrank Hexacode.F W = 3 := by
    have h := Module.finrank_mul_finrank Bit Hexacode.F W
    rw [QuadraticAlgebra.finrank_eq_two, hd] at h
    omega
  let E : W ≃ₗ[Hexacode.F] hexacode :=
    LinearEquiv.ofFinrankEq W hexacode (hdF.trans Hexacode.field_finrank.symm)
  let σ : Representation Hexacode.F HexEvenAutomorphisms W := by
    refine { toFun := fun g => { (τ g).toAddHom with map_smul' := ?_ }
             map_one' := ?_, map_mul' := ?_ }
    · intro r w
      change τ _ (r.re • w + r.im • τ hexEvenZ w) =
        r.re • τ _ w + r.im • τ hexEvenZ (τ _ w)
      rw [map_add, map_smul, map_smul, scalar_commutes]
    · ext w
      exact LinearMap.congr_fun τ.map_one w
    · intro g h
      ext w
      exact LinearMap.congr_fun (τ.map_mul g h) w
  have hσ : Function.Injective σ := by
    intro g h he
    apply hf
    ext w
    exact LinearMap.congr_fun he w
  obtain ⟨b, c, hbc⟩ := EvenImage.exists_twist (coordinateAction σ E)
    (coordinateAction_injective σ E hσ)
  refine ⟨{
    groupEquiv := b
    linearEquiv := (E.trans c).restrictScalars Bit
    intertwines := ?_ }⟩
  intro g w
  have h := hbc g (E w)
  change c (E (τ g (E.symm (E w)))) = Hexacode.evenAction (b g) (c (E w)) at h
  simpa only [E.symm_apply_apply, LinearEquiv.restrictScalars_apply, LinearEquiv.trans_apply] using h
end EvenRecognition
end CFSG.Quasithin.ChapterK.Alternating
