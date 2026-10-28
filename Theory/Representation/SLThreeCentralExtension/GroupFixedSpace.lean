module
public import Theory.Representation.SLThreeCentralExtension.Involutions
public import Theory.Representation.ElementaryPerfectSplit

/-!
# Fixed involutions in elementary extensions of a binary linear-three block

Conjugation on the elementary sixteen descends through the literal block
quotient. Its invariant space is zero when the original block has no fixed
point there. The four-dimensional SL₃(2) calculation makes an involution's
fixed space equal its displacement space. Normality of the block places
every displacement back in that block.

The quotient injection retains the order of the original actor modulo A,
rather than assuming an unrelated quotient involution. The Chapter 14
fusion consumer applies this inside its actual normalizer M.

Source: Aschbacher–Smith, B.4.8(3), printed p.91, applied in 14.4.5,
printed p.1008.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace BinaryLinearThree.NaturalExtension
variable {G : Type*} [_root_.Group G] [Finite G]

/-- In an elementary sixteen extension with no fixed points, the fixed space
of a quotient involution lies in the actual normal block. -/
theorem fixed_involutions_le_block (L A : Subgroup G) [L.Normal] [A.Normal]
    [IsElementaryAbelian 2 A] (hcard : Nat.card A = 16)
    (hfixed : A ⊓ centralizer (L : Set G) = ⊥)
    (e : (L ⧸ A.subgroupOf L) ≃* BinaryLinearThree.Group)
    (y : L) (hy : orderOf (QuotientGroup.mk' A (y : G)) = 2)
    (a : G) (ha : a ∈ A) (hya : Commute (y : G) a) : a ∈ L := by
  let π := QuotientGroup.mk' (A.subgroupOf L)
  let ψ : L →* G ⧸ A := (QuotientGroup.mk' A).comp L.subtype
  have hker : A.subgroupOf L = ψ.ker := by
    ext x
    exact (QuotientGroup.eq_one_iff (x : G)).symm
  let j : (L ⧸ A.subgroupOf L) →* G ⧸ A :=
    (QuotientGroup.kerLift ψ).comp
      (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom
  have hj : Function.Injective j :=
    (QuotientGroup.kerLift_injective ψ).comp
      (QuotientGroup.quotientMulEquivOfEq hker).injective
  have hy₀ : orderOf (π y) = 2 :=
    (orderOf_injective j hj (π y)).symm.trans hy
  let f : L →* MulAut A := (MulAut.conjNormal : G →* MulAut A).comp L.subtype
  have hk : A.subgroupOf L ≤ f.ker := by
    intro l hl
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (l : G) * (x : G) * (l : G)⁻¹ = x
    have hc : Commute (l : G) (x : G) :=
      (show Commute (⟨l,hl⟩ : A) x from Commute.all _ _).map A.subtype
    rw [hc.eq,mul_inv_cancel_right]
  let φ := (QuotientGroup.lift (A.subgroupOf L) f hk).comp e.symm.toMonoidHom
  let ρ := Representation.elementaryRepresentation (p := 2) φ
  have he (l : L) (v : Additive A) :
      (ρ (e (π l)) v).toMul.val = (l : G) * v.toMul.val * (l : G)⁻¹ := by
    change ((QuotientGroup.lift (A.subgroupOf L) f hk) (e.symm (e (π l))) v.toMul : G) = _
    rw [e.symm_apply_apply]
    rfl
  have hz : ρ.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hfixed]
    refine ⟨v.toMul.property,?_⟩
    intro l hl
    have hh := he ⟨l,hl⟩ v
    rw [hv (e (π ⟨l,hl⟩))] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  have hd : Module.finrank (ZMod 2) (Additive A) = 4 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [Nat.card_congr Additive.toMul,hcard,Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm
  let b := e (π y)
  have hb : orderOf b = 2 := (e.orderOf_eq (π y)).trans hy₀
  have hc := involution_codim_of_fixed_zero ρ hd hz b hb
  have hr := (involution_range_eq_fixed ρ hd b hb hc).1
  have haf : Additive.ofMul (⟨a,ha⟩ : A) ∈ Representation.BinaryOffender.fixedSpace ρ (zpowers b) := by
    rw [Representation.BinaryOffender.mem_fixedSpace_zpowers_iff]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [he]
    exact mul_inv_eq_iff_eq_mul.mpr hya.eq
  rw [← hr] at haf
  obtain ⟨v,hv⟩ := haf
  have heq := congrArg (fun w : Additive A => (w.toMul : G)) hv
  simp only [LinearMap.sub_apply, LinearMap.id_apply, toMul_sub,
    div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] at heq
  rw [he] at heq
  change (y : G) * v.toMul.val * (y : G)⁻¹ * v.toMul.val⁻¹ = a at heq
  rw [←heq]
  exact commutator_le_left L ⊤
    (commutator_mem_commutator y.property (mem_top v.toMul.val))
end BinaryLinearThree.NaturalExtension
