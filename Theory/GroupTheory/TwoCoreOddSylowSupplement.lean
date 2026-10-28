module
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.Tactic.Group

/-!
# Odd Sylow supplements through the two-core quotient

If the two-residual of H/O₂(H) is its p-core for an odd prime p, every
Sylow p-subgroup maps isomorphically onto that core. The quotient residual
and the image of a Sylow two-subgroup generate the quotient. Lifting their
product, and absorbing O₂(H) into the two-subgroup, gives H = PT as an
actual elementwise product. No normalization of P by T is asserted.

Source application: Aschbacher–Smith, the construction before 12.2.20,
printed p.802, using B.6.8(2).
-/

public section
namespace Subgroup
variable {H : Type*} [Group H] [Finite H]

theorem odd_prime_subgroup_le_twoResidual {K : Type*} [Group K]
    {p : ℕ} (ho : Odd p) (P : Subgroup K) (hP : IsPGroup p P) :
    P ≤ pResidual 2 K := by
  intro x hx
  apply mem_pResidual_of_orderOf_coprime
  have hc := hP.orderOf_coprime (Nat.coprime_two_right.mpr ho) (⟨x, hx⟩ : P)
  rw [← Subgroup.orderOf_coe] at hc
  exact hc.symm

theorem sylow_map_twoCoreQuotient_eq_odd_core {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hr : pResidual 2 (H ⧸ pCore 2 H) = pCore p (H ⧸ pCore 2 H))
    (P : Sylow p H) :
    (P : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) = pCore p (H ⧸ pCore 2 H) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  apply le_antisymm
  · rw [← hr]
    exact odd_prime_subgroup_le_twoResidual ho _ (P.isPGroup'.map q)
  · exact pCore_isPGroup.le_sylow_of_normal (P.mapSurjective (QuotientGroup.mk'_surjective _))

theorem odd_sylow_two_sylow_factorization {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hr : pResidual 2 (H ⧸ pCore 2 H) = pCore p (H ⧸ pCore 2 H))
    (P : Sylow p H) (T : Sylow 2 H) :
    ∀ x : H, ∃ a ∈ (P : Subgroup H), ∃ t ∈ (T : Subgroup H), x = a * t := by
  let Q := pCore 2 H
  let q := QuotientGroup.mk' Q
  have hq := QuotientGroup.mk'_surjective Q
  have hPQ := sylow_map_twoCoreQuotient_eq_odd_core ho hr P
  have hgen := pResidual_sup_sylow_eq_top (T.mapSurjective hq)
  rw [hr] at hgen
  intro x
  obtain ⟨a, ha, t, ht, he⟩ := mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top (q x))
  rw [← hPQ] at ha
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨t₀, ht₀, rfl⟩ := ht
  change q a₀ * q t₀ = q x at he
  have hk : a₀⁻¹ * x * t₀⁻¹ ∈ Q := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (a₀⁻¹ * x * t₀⁻¹) = 1
    rw [map_mul, map_mul, map_inv, map_inv, ← he]
    group
  have hQT : Q ≤ (T : Subgroup H) := pCore_isPGroup.le_sylow_of_normal T
  refine ⟨a₀, ha₀, a₀⁻¹ * x, ?_, by group⟩
  simpa only [inv_mul_cancel_right] using (T : Subgroup H).mul_mem (hQT hk) ht₀

omit [Finite H] in
theorem quotient_twoCore_injective_on_odd_sylow {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (P : Sylow p H) :
    Function.Injective ((QuotientGroup.mk' (pCore 2 H)).comp (P : Subgroup H).subtype) := by
  have hp2 : p ≠ 2 := by intro he; subst p; exact ho.not_two_dvd_nat (dvd_refl 2)
  have hd := IsPGroup.disjoint_of_ne p 2 hp2 (P : Subgroup H) (pCore 2 H)
    P.isPGroup' pCore_isPGroup
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  apply Subtype.ext
  exact hd.le_bot ⟨x.property, (QuotientGroup.eq_one_iff (x : H)).mp hx⟩

end Subgroup
