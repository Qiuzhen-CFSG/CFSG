module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import Theory.GroupTheory.BinarySquareForm
public import Theory.ElementaryAbelian.Extraspecial

/-!
# The source power form on the literal quotient U/Z

Extraspeciality and the identification Z(U)=Z construct the binary quadratic
form on the original quotient. Its polar is the commutator and is
nondegenerate. The original H-conjugation action preserves the form, and
zero values are exactly the cosets represented by involutions or identity.

Source: Aschbacher–Smith, 15.3.55 and 15.3.56(1), printed p.1147.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open Recognition
variable {G : Type*} [Group G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

/-- The quotient map with exactly the multiplicative/additive tags required
by the general square-form construction. -/
def powerCoordinates : closureU Z ZS →* Multiplicative (Space Z ZS) where
  toFun x := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' _ x))
  map_one' := congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x)) (map_one (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS))))
  map_mul' x y := congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x))
    (map_mul (QuotientGroup.mk' _) x y)

/-- The source extraspecial group supplies the power form without a choice
of model or a hypothesis about the later recognized action. -/
theorem exists_power_form [IsExtraspecial 2 (closureU Z ZS)]
    (hcenter : center (closureU Z ZS) = Z.subgroupOf (closureU Z ZS)) :
    ∃ q : QuadraticForm (ZMod 2) (Space Z ZS),
      q.polarBilin.Nondegenerate ∧
      (∀ h : centralizerH Z, ∀ w : VectorQuotient Z ZS,
        q (Additive.ofMul (quotientAction Z ZS h w)) = q (Additive.ofMul w)) ∧
      (∀ x : closureU Z ZS,
        q (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) x)) = 0 ↔
          x ^ 2 = 1) ∧
      (∀ x y : closureU Z ZS,
        q.polarBilin
          (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) x))
          (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) y)) = 0 ↔
            Commute x y) := by
  let U := closureU Z ZS
  let c := powerCoordinates Z ZS
  have hc : c.ker = center U := by
    rw [hcenter]
    ext x
    exact QuotientGroup.eq_one_iff x
  have hsurj : Function.Surjective c := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) v.toAdd.toMul
    exact ⟨x, congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x)) hx⟩
  have h2 : ∀ z ∈ center U, z ^ 2 = 1 := by
    intro z hz
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hz⟩ : center U)))
    simpa only [IsExtraspecial.center_order_p 2 U, coe_pow, coe_one] using hh
  let χ : center U ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq (IsExtraspecial.center_order_p 2 U) (by simp)
  let q := Theory.GroupTheory.BinarySquareForm.quadraticForm c hc hsurj h2 χ.toMonoidHom
  have hzero (x : U) :
      q (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) x)) = 0 ↔ x ^ 2 = 1 := by
    rw [show q (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) x)) =
      (χ ⟨x ^ 2, Theory.GroupTheory.BinarySquareForm.square_mem_center c hc x⟩).toAdd from
        Theory.GroupTheory.BinarySquareForm.quadraticForm_coordinates c hc hsurj h2 χ.toMonoidHom x]
    change χ _ = 1 ↔ _
    rw [χ.map_eq_one_iff]
    exact Subtype.ext_iff
  have hpolar (x y : U) :
      q.polarBilin (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) x))
        (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) y)) = 0 ↔ Commute x y := by
    rw [show q.polarBilin (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) x))
        (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) y)) =
        (χ ⟨⁅x,y⁆, Theory.GroupTheory.BinarySquareForm.commutator_mem_center c hc x y⟩).toAdd from
      Theory.GroupTheory.BinarySquareForm.polarBilin_coordinates c hc hsurj h2 χ.toMonoidHom x y]
    change χ _ = 1 ↔ _
    rw [χ.map_eq_one_iff, Subtype.ext_iff, coe_one]
    exact commutatorElement_eq_one_iff_mul_comm
  have hsep : q.polarBilin.SeparatingLeft := by
    intro w hw
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w.toMul
    have he : w = Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) x) :=
      congrArg Additive.ofMul hx.symm
    subst w
    have hxcenter : x ∈ center U := mem_center_iff.mpr (fun y =>
      ((hpolar x y).mp (hw (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) y)))).eq.symm)
    exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff x).mpr (hcenter ▸ hxcenter))
  refine ⟨q, ⟨hsep, ?_⟩, ?_, hzero, hpolar⟩
  · intro w hw
    apply hsep w
    intro v
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact hw v
  · intro h w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
    rw [quotientAction_mk]
    let a : MulAut U := U.normalizerMonoidHom ⟨h, H_normalizes_closureU Z ZS h.property⟩
    have he : q (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) (a x))) = 0 ↔
        q (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) x)) = 0 := by
      rw [hzero, hzero, ← map_pow, a.map_eq_one_iff]
    have binary : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
    exact binary _ _ he

/-- The action by H/O₂(H) has the same invariant form once source 15.3.48(3)
identifies its kernel. This is the representation used by the recognition consumer. -/
theorem exists_actor_power_form [IsExtraspecial 2 (closureU Z ZS)]
    (hcenter : center (closureU Z ZS) = Z.subgroupOf (closureU Z ZS))
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    ∃ q : QuadraticForm (ZMod 2) (Space Z ZS),
      q.polarBilin.Nondegenerate ∧
      (∀ a w, q (actorRepresentation Z ZS hkernel a w) = q w) ∧
      (∀ x : closureU Z ZS,
        q (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) x)) = 0 ↔
          x ^ 2 = 1) ∧
      (∀ x y : closureU Z ZS,
        q.polarBilin
          (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) x))
          (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) y)) = 0 ↔
            Commute x y) := by
  obtain ⟨q, hn, hi, hp, hb⟩ := exists_power_form Z ZS hcenter
  refine ⟨q, hn, ?_, hp, hb⟩
  intro a w
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (centralizerH Z)) a
  exact hi h w.toMul

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
