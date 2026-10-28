module

public import Theory.GroupTheory.ElementaryQuotientCocycles
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Fixed lifts through elementary kernels

For an involutory actor, the defect of a representative of a fixed quotient
element is an elementary-kernel cocycle. A square-root fixed subgroup in the
kernel makes that cocycle a coboundary. Correcting the representative by the
coboundary gives a fixed lift. A nontrivial fixed quotient therefore supplies
a fixed element outside the kernel.

The quotient and restricted actions are literal homomorphisms, so this
applies directly to the actions on J(S) and O₂(H) in the field-involution
branch of Aschbacher–Smith, Lemmas 2.4.12(2) and 2.4.21(2), printed
pp.532 and 536 of the manuscript of 1 March 2004.
-/

public section

namespace Theory.GroupTheory
open Subgroup
open scoped IsMulCommutative
variable {R : Type*} [Group R] [Finite R]

theorem exists_fixed_quotient_lift_of_elementary_kernel
    (N : Subgroup R) [N.Normal] [IsElementaryAbelian 2 N]
    (α : R →* R) (hα : Function.Involutive α) (hN : ∀ x ∈ N, α x ∈ N)
    (hcN : Nat.card ((α.restrict hN).eqLocus (MonoidHom.id N)) ^ 2 = Nat.card N)
    (v : R ⧸ N) (hv : QuotientGroup.map N N α hN v = v) :
    ∃ r : R, α r = r ∧ QuotientGroup.mk' N r = v := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N v
  have hdef : x⁻¹ * α x ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (x⁻¹ * α x) = 1
    rw [map_mul, map_inv]
    change QuotientGroup.mk' N (α x) = QuotientGroup.mk' N x at hv
    rw [hv, inv_mul_cancel]
  let d : N := ⟨x⁻¹ * α x, hdef⟩
  have hinv (a : N) : a⁻¹ = a := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 N) a
  have hd : (α.restrict hN) d = d := by
    calc
      (α.restrict hN) d = d⁻¹ := by
        apply Subtype.ext
        change α (x⁻¹ * α x) = (x⁻¹ * α x)⁻¹
        rw [map_mul, map_inv, hα, mul_inv_rev, inv_inv]
      _ = d := hinv d
  have hαN : ∀ a : N, (α.restrict hN) ((α.restrict hN) a) = a :=
    fun a => Subtype.ext (hα a.val)
  obtain ⟨y, hy⟩ := elementary_fixed_is_coboundary (A := N) (α.restrict hN) hαN hcN d hd
  have he := congrArg (fun z : N => z.val) hy
  change x⁻¹ * α x = y.val * α (y.val⁻¹) at he
  rw [map_inv] at he
  refine ⟨x * y.val, ?_, ?_⟩
  · rw [map_mul]
    calc
      α x * α y.val = x * (x⁻¹ * α x) * α y.val := by group
      _ = x * y.val := by rw [he]; group
  · have hyN : QuotientGroup.mk' N y.val = 1 := (QuotientGroup.eq_one_iff y.val).mpr y.property
    rw [map_mul, hyN, mul_one]

theorem exists_fixed_outside_of_elementary_kernel
    (N : Subgroup R) [N.Normal] [IsElementaryAbelian 2 N]
    (α : R →* R) (hα : Function.Involutive α) (hN : ∀ x ∈ N, α x ∈ N)
    (hcN : Nat.card ((α.restrict hN).eqLocus (MonoidHom.id N)) ^ 2 = Nat.card N)
    (hcQ : 1 < Nat.card ((QuotientGroup.map N N α hN).eqLocus
      (MonoidHom.id (R ⧸ N)))) :
    ∃ r : R, α r = r ∧ r ∉ N := by
  let C := (QuotientGroup.map N N α hN).eqLocus (MonoidHom.id (R ⧸ N))
  have hC : C ≠ ⊥ := by
    intro h
    have hcard : Nat.card C = 1 := h ▸ Subgroup.card_bot
    change 1 < Nat.card C at hcQ
    omega
  obtain ⟨v, hv⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hC
  obtain ⟨r, hr, he⟩ := exists_fixed_quotient_lift_of_elementary_kernel N α hα hN hcN v.val v.property
  refine ⟨r, hr, ?_⟩
  intro hrN
  exact hv (Subtype.ext (he.symm.trans ((QuotientGroup.eq_one_iff r).mpr hrN)))
end Theory.GroupTheory
