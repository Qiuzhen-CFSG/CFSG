module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedAction
public import Theory.Representation.BinaryPermutation.FiveCentralExtension
/-!
# No fixed vector for the deleted tensor component

The sum of the twenty three-cycle operators is the identity on the binary
five-letter core and zero on a fixed vector. The tensor coordinates identify
the restriction to A₅ with two copies of that core. Thus the actual solvable
residual cannot centralize a subgroup with nonzero image in U/Z(U).

This supplies the action obstruction in the deleted-tensor residual-core
argument, without identifying U with O₂(H).
Source: Aschbacher--Smith 14.4.10(3), printed p.1011.
-/

public section
open Subgroup TensorProduct Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.TensorDeleted
open LargerDimension.Tensor BinaryPermutation

private theorem core_fixed_zero (v : core (Fin 5))
    (hv : ∀ a : AltFive, coreRepresentation (Fin 5) a.val v = v) : v = 0 := by
  have h := FiveCentralExtension.core_sum v
  have hs : (∑ g ∈ FiveCentralExtension.cubes, coreRepresentation (Fin 5) g v) = 0 := by
    calc
      _ = ∑ _g ∈ FiveCentralExtension.cubes, v :=
        Finset.sum_congr rfl (fun g hg => hv ⟨g, FiveCentralExtension.cubes_even g hg⟩)
      _ = 0 := by
        rw [Finset.sum_const, FiveCentralExtension.cubes_card,
          ← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
        change (20 : ZMod 2) • v = 0
        rw [show (20 : ZMod 2) = 0 from rfl, zero_smul]
  exact h.symm.trans hs

variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The second tensor factor has no nonzero common fixed vector. -/
theorem fixed_tensor_zero (σ : Representation (ZMod 2) D W)
    (hdel : IsDeletedFour hAD σ) (v : core (Fin 3) ⊗[ZMod 2] W)
    (hv : ∀ a : AltFive, sourceTensorAction σ (1, inclusion hAD a) v = v) : v = 0 := by
  obtain ⟨f,hf⟩ := hdel
  let e := (TensorProduct.comm (ZMod 2) (core (Fin 3)) W).trans
    (TensorProduct.congr f (LinearEquiv.refl (ZMod 2) (core (Fin 3))))
  have he (a : AltFive) (w : core (Fin 3) ⊗[ZMod 2] W) :
      e (sourceTensorAction σ (1, inclusion hAD a) w) =
        ThreeTensor.action (coreRepresentation (Fin 5)) (a.val, 1) (e w) := by
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul n w =>
      change f (σ (inclusion hAD a) w) ⊗ₜ[ZMod 2] _ = _
      rw [hf]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  let p := ThreeTensor.pairEquiv (e v)
  have hp (a : AltFive) :
      (coreRepresentation (Fin 5) a.val p.1, coreRepresentation (Fin 5) a.val p.2) = p := by
    have hh := congrArg (fun w => ThreeTensor.pairEquiv (e w)) (hv a)
    rw [he, ThreeTensor.pairEquiv_equivariant] at hh
    exact hh
  apply e.injective
  apply ThreeTensor.pairEquiv.injective
  rw [map_zero, map_zero]
  exact Prod.ext (core_fixed_zero p.1 (fun a => congrArg Prod.fst (hp a)))
    (core_fixed_zero p.2 (fun a => congrArg Prod.snd (hp a)))

variable {G : Type*} [Group G] [Finite G] {H U P : Subgroup G}

/-- Centralization by the literal H∞ forces zero image in the marked quotient. -/
theorem image_eq_bot_of_component_centralizes
    (c : CaseFiveCoordinates hAD (V := W) H U)
    (hdel : IsDeletedFour hAD c.constituent)
    (hc : component H ≤ centralizer (P : Set G)) : c.image P = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  apply fixed_tensor_zero c.constituent hdel v
  intro a
  have ha : (1, inclusion hAD a) ∈ (star H (component H)).map c.actor.toMonoidHom := by
    rw [star_component_marked hAD c.actor]
    exact ⟨rfl, a.property⟩
  obtain ⟨x, ⟨h, hh, rfl⟩, hx⟩ := ha
  change c.actor (QuotientGroup.mk' (pCore 2 H) h) = (1, inclusion hAD a) at hx
  obtain ⟨u, hu, rfl⟩ := (c.mem_image P v).mp hv
  have hcu : (h : G) * (u : G) * (h : G)⁻¹ = u := by
    have hcomm := mem_centralizer_iff.mp (hc hh) u hu
    change (u : G) * (h : G) = (h : G) * (u : G) at hcomm
    calc
      _ = (u : G) * (h : G) * (h : G)⁻¹ := by rw [← hcomm]
      _ = u := mul_inv_cancel_right _ _
  have hhq := c.equivariant h u
  have he : (⟨(h : G) * (u : G) * (h : G)⁻¹,
      le_normalizer_iff.mp c.H_normalizes_U h h.property u u.property⟩ : U) = u :=
    Subtype.ext hcu
  rw [he, hx] at hhq
  exact (congrArg Multiplicative.toAdd hhq).symm
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.TensorDeleted
