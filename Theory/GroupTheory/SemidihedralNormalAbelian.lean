module
public import Theory.GroupTheory.SemidihedralStandardModel
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-!
# Abelian normal subgroups and index-two powers in semidihedral sixteen

One checked sixteen-element commutation identity shows that a maximal
rotation centralizes every normal abelian subgroup. A nonabelian subgroup
of order eight has exponent dividing four, since an element of order eight
would generate it. The local concrete semidirect product is transported to
the standard semidihedral model through its checked presentation.

The finite identity is checked by the kernel; the element-order bound is
structural. This is the exceptional model calculation in the abelian-core
branch of Aschbacher--Smith 2.5.21, printed p.565.
-/

public section
namespace Semidihedral.AbelianCore
open Subgroup
private abbrev C8 := Multiplicative (ZMod 8)
private abbrev C2 := Multiplicative (ZMod 2)
private def twist : MulAut C8 where
  toFun x := .ofAdd (3 * x.toAdd)
  invFun x := .ofAdd (3 * x.toAdd)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel
private def action : C2 →* MulAut C8 where
  toFun i := twist ^ i.toAdd.val
  map_one' := rfl
  map_mul' := by intro i j; ext x; revert i j x; decide +kernel
private abbrev D := C8 ⋊[action] C2
private abbrev r : D := SemidirectProduct.inl (.ofAdd 1)
private abbrev s : D := SemidirectProduct.inr (.ofAdd 1)
private instance : Fintype D := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
private theorem d_equiv : Nonempty (D ≃* StandardModel 4 (by omega)) := by
  apply standardModel_equiv_of_presentation (by omega : 4 ≤ 4) r s
  · rw [orderOf_injective _ SemidirectProduct.inl_injective, orderOf_ofAdd_eq_addOrderOf,
      ZMod.addOrderOf_one]
    norm_num
  · rw [orderOf_injective _ SemidirectProduct.inr_injective, orderOf_ofAdd_eq_addOrderOf,
      ZMod.addOrderOf_one]
  · decide +kernel
  · apply top_le_iff.mp
    intro x _
    have hc : ∀ x : D, ∃ i j : Fin 8, x = r ^ i.val * s ^ j.val := by decide +kernel
    obtain ⟨i, j, rfl⟩ := hc x
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (subset_closure (by simp)) _)
  · rw [SemidirectProduct.card]; simp



private theorem normal_abelian_element : ∀ b : D,
    b * (r * b * r⁻¹) = (r * b * r⁻¹) * b → r * b = b * r := by decide +kernel

private theorem rotation_centralizes (B : Subgroup D) [B.Normal] [IsMulCommutative B] :
    r ∈ centralizer (B : Set D) := by
  intro b hb
  have hconj := (inferInstance : B.Normal).conj_mem b hb r
  exact (normal_abelian_element b (B.le_centralizer hconj b hb)).symm

private theorem abstract_pow_four {P : Type*} [Group P] [Finite P]
    (hc : Nat.card P = 8) (hn : ¬ IsMulCommutative P) (d : P) : d ^ 4 = 1 := by
  have hd : orderOf d ∣ 2 ^ 3 := by simpa only [hc, Nat.reducePow] using orderOf_dvd_natCard d
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  by_cases hk3 : k = 3
  · have ho : orderOf d = Nat.card P := by simpa only [hk3, hc, Nat.reducePow] using he
    exact (hn (isCyclic_of_orderOf_eq_card d ho).isMulCommutative).elim
  · apply orderOf_dvd_iff_pow_eq_one.mp
    rw [he]
    exact pow_dvd_pow 2 (by omega : k ≤ 2)

private theorem index_two_pow_four (N : Subgroup D)
    (hi : N.index = 2) (hn : ¬ IsMulCommutative N) : ∀ d ∈ N, d ^ 4 = 1 := by
  have hc : Nat.card N = 8 := by
    have h := N.index_mul_card
    have hd : Nat.card D = 16 := by rw [SemidirectProduct.card]; simp
    rw [hi, hd] at h
    omega
  intro d hd
  exact congrArg Subtype.val (abstract_pow_four hc hn (⟨d, hd⟩ : N))

/-- A normal abelian subgroup of SD₁₆ is centralized by an element of order eight. -/
theorem exists_eight_centralizing_normal_abelian
    (B : Subgroup (StandardModel 4 (by decide))) [B.Normal] [IsMulCommutative B] :
    ∃ r : StandardModel 4 (by decide), orderOf r = 8 ∧ r ∈ centralizer (B : Set _) := by
  obtain ⟨e⟩ := d_equiv
  let N := B.comap e.toMonoidHom
  let : N.Normal := inferInstance
  let : IsMulCommutative N := B.comap_injective_isMulCommutative e.injective
  have hr := rotation_centralizes N
  refine ⟨e r, ?_, ?_⟩
  · rw [e.orderOf_eq]
    rw [orderOf_injective _ SemidirectProduct.inl_injective, orderOf_ofAdd_eq_addOrderOf,
      ZMod.addOrderOf_one]
  · intro b hb
    obtain ⟨c, rfl⟩ := e.surjective b
    simpa only [map_mul] using congrArg e (hr c hb)

/-- Nonabelian index-two subgroups of SD₁₆ have exponent dividing four. -/
theorem nonabelian_index_two_pow_four
    (N : Subgroup (StandardModel 4 (by decide)))
    (hi : N.index = 2) (hn : ¬ IsMulCommutative N) : ∀ d ∈ N, d ^ 4 = 1 := by
  obtain ⟨e⟩ := d_equiv
  let B := N.comap e.toMonoidHom
  have hb : B.index = 2 := (index_comap_of_surjective _ e.surjective).trans hi
  have hbn : ¬ IsMulCommutative B := by
    intro hh
    apply hn
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have ha : e.symm (a : StandardModel 4 (by decide)) ∈ B := by change e (e.symm _) ∈ N; simp
    have hb : e.symm (b : StandardModel 4 (by decide)) ∈ B := by change e (e.symm _) ∈ N; simp
    have hc := congrArg e (congrArg Subtype.val (hh.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩))
    simpa only [coe_mul, map_mul, e.apply_symm_apply] using hc
  intro d hd
  obtain ⟨b, rfl⟩ := e.surjective d
  simpa only [map_pow, map_one] using congrArg e (index_two_pow_four B hb hbn b hd)
end Semidihedral.AbelianCore
