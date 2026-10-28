module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Common
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent
public import Theory.GroupTheory.GeneralizedFitting.ComponentInvolutionAction
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.CComponent.TwoComponent
public import FeitThompson.FinalTheorem

/-!
# The original marked involution on an ordinary component

An element centralizing a Sylow two-subgroup normalizes every ordinary
component: the component's simple central quotient has even order. Its
characteristic-two centralizer excludes trivial action and the component
commutator dichotomy gives [L,z]=L. The actual subnormal Sylow intersection
is fixed pointwise. Restricting the subnormal chain to C_H(z) transfers
characteristic two to the full fixed group, and subnormal odd-core
containment transfers inversion.

This constructs all four marked inputs used by the local classifier in
Aschbacher–Smith 1.1.5(3), printed pp.501–503. No quotient fixed-point or
classification premise is added.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
variable {H : Type*} [Group H] [Finite H]

/-- The actual component action, its original fixed Sylow, and full
commutator generation from the ambient local hypotheses. -/
public theorem component_marked (S : Sylow 2 H) (z : H) (hz : orderOf z = 2)
    (hfix : ∀ s ∈ S, s * z = z * s)
    (hC : HasCharacteristicTwo (centralizer ({z} : Set H)))
    (hinv : ∀ x ∈ pPrimeCore 2 H, z * x * z⁻¹ = x⁻¹)
    (D : Subgroup H) (hD : IsComponent H D) :
    ∃ (α : MulAut D) (P : Sylow 2 D),
      (∀ x : D, (α x : H) = z * x * z⁻¹) ∧ MarkedInvolution α P ∧
      ⁅D, zpowers z⁆ = D := by
  let : IsQuasisimple D := hD.2
  have heven : 2 ∣ Nat.card (D ⧸ center D) := by
    by_contra hn
    let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    let : Group.IsPerfect (D ⧸ center D) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact Group.IsPerfect.not_isSolvable (D ⧸ center D)
      (odd_order_theorem _ (Nat.not_even_iff_odd.mp (fun h => hn h.two_dvd)))
  have hzC : z ∈ centralizer (S : Set H) := by
    intro s hs
    exact hfix s hs
  have hzN : z ∈ normalizer (D : Set H) :=
    hD.centralizes_sylow_normalizes S heven (zpowers_le.mpr hzC) (mem_zpowers z)
  let zn : normalizer (D : Set H) := ⟨z, hzN⟩
  let α := D.normalizerMonoidHom zn
  have ha (x : D) : (α x : H) = z * x * z⁻¹ := rfl
  have ha2 : α ^ 2 = 1 := by
    have hzn : zn ^ 2 = 1 := Subtype.ext (by
      change z ^ 2 = 1
      simpa only [hz] using pow_orderOf_eq_one z)
    change (D.normalizerMonoidHom zn) ^ 2 = 1
    rw [← map_pow, hzn, map_one]
  have hane : α ≠ 1 := by
    intro he
    apply hD.not_centralizes_of_twoCore_centralizer z hC
    intro x hx
    have hh : z * x * z⁻¹ = x := by
      have h := congrArg (fun a : MulAut D => (a ⟨x, hx⟩ : H)) he
      exact h
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal D hD.1
  have hPfix : ∀ x ∈ P, α x = x := by
    intro x hx
    have hxS : (x : H) ∈ S := by
      have hxD : x ∈ (S : Subgroup H).subgroupOf D := by rw [← hP]; exact hx
      exact hxD
    apply Subtype.ext
    rw [ha, ← hfix x hxS, mul_inv_cancel_right]
  let C := centralizer ({z} : Set H)
  have hcf (x : D) : (x : H) ∈ C ↔ α x = x := by
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply Subtype.ext
      rw [ha, ← h, mul_inv_cancel_right]
    · intro h
      exact (mul_inv_eq_iff_eq_mul.mp (ha x |>.symm.trans (congrArg Subtype.val h))).symm
  let e : D.subgroupOf C ≃* α.fixedSubgroup := {
    toFun x := ⟨⟨x, x.property⟩, (MulAut.mem_fixedSubgroup _ _).mpr ((hcf _).mp x.val.property)⟩
    invFun x := ⟨⟨x, (hcf _).mpr ((MulAut.mem_fixedSubgroup _ _).mp x.property)⟩, x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hfixed : HasCharacteristicTwo α.fixedSubgroup :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
      (subnormal_core_selfCentralizing hC (D.subgroupOf C) hD.1.subgroupOf)
  refine ⟨α, P, ha, ⟨orderOf_eq_prime ha2 hane, hPfix, hfixed, ?_⟩,
    hD.commutator_eq_self_of_twoCore_centralizer z hzN hC⟩
  intro x hx
  apply Subtype.ext
  rw [ha]
  exact hinv x (hD.1.pPrimeCore_map_le (mem_map_of_mem D.subtype hx))
end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
