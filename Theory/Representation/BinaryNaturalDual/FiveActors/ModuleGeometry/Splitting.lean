module

public import Theory.Representation.BinaryNaturalDual.FiveActors.ModuleGeometry.Diagonal

/-!
# Compatible line-plus-four-space coordinates for the outer fixed module

An explicit inner conjugator transports the fixed subgroup to inverse
transpose. Restriction to the existing symplectic coordinates gives the
actual S₆ action; the same conjugator transports the fixed vector space.
Evaluation of the hyperbolic quadratic form is the first coordinate.

Source: Aschbacher–Smith, H.9.2(1), printed p.390 (PDF p.401).
-/

@[expose] public section

open Matrix BinaryLinear BinaryLinear.OuterCyclic
open BinaryNaturalDual.AdaptedPair
open Theory.SpecificGroups.SymmetricSix
namespace BinaryNaturalDual.FiveActors.ModuleGeometry
open BinaryLinear.SixSylowActors.Five

variable (t : M) (g : G) (hg : MulAut.conj (MulAut.conj g) t = graphLinear 5)

include hg in
private theorem normalizes_group (x : G) :
    MulAut.conj g (t x) = graphLinear 5 (MulAut.conj g x) := by
  have h := congrArg (fun a : M => a (MulAut.conj g x)) hg
  change MulAut.conj g (t ((MulAut.conj g).symm (MulAut.conj g x))) = _ at h
  simpa only [MulEquiv.symm_apply_apply] using h

noncomputable def normalizedFixedEquiv : t.fixedSubgroup ≃* (graphLinear 5).fixedSubgroup where
  toFun a := ⟨MulAut.conj g a.val, by
    rw [MulAut.mem_fixedSubgroup, ← normalizes_group t g hg,
      (MulAut.mem_fixedSubgroup t a.val).mp a.property]⟩
  invFun a := ⟨(MulAut.conj g).symm a.val, by
    rw [MulAut.mem_fixedSubgroup]
    apply (MulAut.conj g).injective
    rw [normalizes_group t g hg, MulEquiv.apply_symm_apply,
      (MulAut.mem_fixedSubgroup (graphLinear 5) a.val).mp a.property]⟩
  left_inv a := Subtype.ext ((MulAut.conj g).symm_apply_apply a.val)
  right_inv a := Subtype.ext ((MulAut.conj g).apply_symm_apply a.val)
  map_mul' a b := Subtype.ext ((MulAut.conj g).map_mul a.val b.val)

@[simp] theorem normalizedFixedEquiv_apply (a : t.fixedSubgroup) :
    (normalizedFixedEquiv t g hg a).val = g * a.val * g⁻¹ := rfl

noncomputable def centralizerSixEquiv : innerCentralizer t ≃* S6 :=
  (fixedInnerCentralizerEquiv t).symm.trans
    ((normalizedFixedEquiv t g hg).trans Standard.fixedEquiv.symm)

private theorem standard_action (a : (graphLinear 5).fixedSubgroup)
    (c : ZMod 2) (v : NaturalModule) :
    a.val (Standard.coordinates (c, v)) =
      Standard.coordinates (c, polarAction (Standard.fixedEquiv.symm a) v) := by
  rw [Standard.fixedSpEquiv_action]
  congr 1
  change (_, (Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv
    (Standard.fixedEquiv.symm a)).val *ᵥ v) = _
  rw [Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv_apply,
    polarRepresentation_apply]

variable (d : CoordinateAction 5) (ht : t ^ 2 = 1) (hout : t ∉ L)

noncomputable def splitEquiv : (ZMod 2 × NaturalModule) ≃ₗ[ZMod 2]
    fixedSpace (linearAction d t) :=
  Standard.coordinates.trans (g.symm.trans (diagonal d t ht hout))

@[simp] theorem splitEquiv_apply (c : ZMod 2) (v : NaturalModule) :
    splitEquiv t g d ht hout (c, v) =
      diagonal d t ht hout (g.symm (Standard.coordinates (c, v))) := rfl

theorem splitEquiv_equivariant (a : innerCentralizer t) (c : ZMod 2) (v : NaturalModule) :
    (splitEquiv t g d ht hout (c, polarAction (centralizerSixEquiv t g hg a) v) : V) =
      d.representation a.val (splitEquiv t g d ht hout (c, v)) := by
  rw [splitEquiv_apply, splitEquiv_apply, ← diagonal_equivariance]
  congr 2
  apply g.injective
  rw [g.apply_symm_apply]
  have hh := standard_action (normalizedFixedEquiv t g hg
    ((fixedInnerCentralizerEquiv t).symm a)) c v
  change (g * centralizerNatural t a * g⁻¹) (Standard.coordinates (c, v)) = _ at hh
  simpa only [centralizerSixEquiv, MulEquiv.trans_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv] using hh.symm

include hg in
private theorem normalizes_action (v : V) :
    linearAction d (MulAut.conj g) (linearAction d t v) =
      coordinateSwap 5 (linearAction d (MulAut.conj g) v) := by
  have he : MulAut.conj g * t = graphLinear 5 * MulAut.conj g := by
    have h := congrArg (fun a : M => a * MulAut.conj g) hg
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using h
  have h := congrArg (fun a : M => linearAction d a v) he
  simpa only [map_mul, LinearEquiv.mul_apply, linearAction_apply, d.on_graph] using h

include hg in
theorem splitEquiv_quadratic (c : ZMod 2) (v : NaturalModule) :
    quadratic (splitEquiv t g d ht hout (c, v) : V) = c := by
  have hnorm : linearAction d (MulAut.conj g)
      (splitEquiv t g d ht hout (c, v) : V) =
        (Standard.coordinates (c, v), dotProductEquiv (ZMod 2) (Fin 5) (Standard.coordinates (c, v))) := by
    change linearAction d (MulAut.conj g)
      ((g.symm (Standard.coordinates (c, v)), 0) +
        linearAction d t (g.symm (Standard.coordinates (c, v)), 0)) = _
    rw [map_add, normalizes_action t g hg d]
    rw [linearAction_inner_pair]
    simp [coordinateSwap_apply]
  have hq := quadratic_innerActor d (MulAut.conj g) ⟨g, rfl⟩
    (splitEquiv t g d ht hout (c, v) : V)
  rw [hnorm, quadratic_apply] at hq
  change dotProduct (Standard.coordinates (c, v)) (Standard.coordinates (c, v)) = _ at hq
  rw [Standard.coordinates_form, polarForm_alt, add_zero] at hq
  have hc : c * c = c := (by decide : ∀ a : ZMod 2, a * a = a) c
  exact hq.symm.trans hc

end BinaryNaturalDual.FiveActors.ModuleGeometry
