module
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.ResidualNine
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.FactorCoordinates

/-!
# A fixed cubic in the quaternion swap quotient

The two-residual of the square-wreath group has order nine. A kernel-checked
table on its 72 elements produces a nonidentity fixed cubic for each
involutory factor swap. An injective quaternion-action quotient whose
residual image has order nine contains this whole residual. Pulling the
fixed cubic back retains the original quotient map and residual membership.

The order-32 Chapter 14 consumer uses this element for the central-kernel
lifting contradiction. Source: Aschbacher–Smith, proof of 14.4.4(6), p.1007.
-/

public section
open Subgroup
namespace BinaryFourPlus
private instance : DecidableEq Wreath :=
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).injective.decidableEq
private instance : Fintype Wreath :=
  Fintype.ofEquiv _ (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).symm
private theorem fixed_cubic_table : ∀ w : Wreath,
    w.right ≠ 1 → w ^ 2 = 1 →
      ∃ c : Wreath, c ^ 3 = 1 ∧ c ≠ 1 ∧ w*c=c*w := by
  decide +kernel

/-- An involutory factor swap fixes a nonidentity cubic in the actual residual. -/
theorem exists_fixed_cubic_of_swap (w : Wreath)
    (hs : w.right ≠ 1) (h2 : w ^ 2 = 1) :
    ∃ c ∈ pResidual 2 Wreath, c ^ 3 = 1 ∧ c ≠ 1 ∧ Commute w c := by
  obtain ⟨c,h3,hn,hc⟩ := fixed_cubic_table w hs h2
  exact ⟨c, mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one h3)),h3,hn,hc⟩
end BinaryFourPlus

namespace Subgroup.QuaternionCentralProductData
variable {Q H : Type*} [Group Q] [Finite Q] [Group H] [Finite H]
omit [Finite H] in
/-- Pull the fixed cubic into the literal residual and central-quotient map. -/
theorem fixed_cubic_in_residual_quotient_of_swap (d : QuaternionCentralProductData Q)
    (α : H →* MulAut Q) (N : Subgroup H) [N.Normal]
    (hk : ((quotientAut (center Q)).comp α).ker = N)
    (hc : Nat.card ((pResidual 2 H).map (QuotientGroup.mk' N)) = 9)
    (a : H) (ha : a ^ 2 = 1) (hswap : d.left.map (α a).toMonoidHom = d.right) :
    ∃ k ∈ pResidual 2 H, QuotientGroup.mk' N k ≠ 1 ∧
      (QuotientGroup.mk' N k) ^ 3 = 1 ∧
      Commute (QuotientGroup.mk' N a) (QuotientGroup.mk' N k) := by
  let π := QuotientGroup.mk' N
  obtain ⟨f,hf,he⟩ := d.wreath_quotient_embedding α N hk
  have hr : ((pResidual 2 H).map π).map f = pResidual 2 BinaryFourPlus.Wreath := by
    apply eq_of_le_of_card_ge
    · exact (map_mono (map_pResidual_le 2 π)).trans (map_pResidual_le 2 f)
    · rw [card_map_of_injective hf, hc, BinaryFourPlus.wreath_residual_card]
  have hswap' : (f (π a)).right ≠ 1 := by
    rw [he]
    intro hn
    have hh := (d.quotientWreathAction_right_eq_one_iff (α a)).mp hn
    rw [hswap] at hh
    have hcQ := d.card
    have hlc : Nat.card d.left = 8 := by
      rw [Nat.card_congr d.left_model.some.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
    have hs := d.span
    rw [hh,sup_idem] at hs
    rw [hs,card_top] at hlc
    omega
  obtain ⟨c,hcR,hc3,hcn,hca⟩ := BinaryFourPlus.exists_fixed_cubic_of_swap (f (π a))
    hswap' (by rw [←map_pow,←map_pow,ha,map_one,map_one])
  rw [←hr] at hcR
  obtain ⟨b,⟨k,hkK,rfl⟩,hkc⟩ := hcR
  refine ⟨k,hkK,?_,?_,?_⟩
  · intro hn
    apply hcn
    rw [←hkc,hn,map_one]
  · apply hf
    rw [map_pow,hkc,hc3,map_one]
  · change Commute (π a) (π k)
    apply hf
    simpa only [map_mul,hkc] using hca.eq
end Subgroup.QuaternionCentralProductData
