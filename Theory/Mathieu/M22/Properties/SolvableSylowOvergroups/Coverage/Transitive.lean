module

public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.GroupTheory.SolvableRadical.AbelianCharacteristic
public import Theory.GroupTheory.SolvableRadical.AbelianCharacteristic.Elementary
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Excluding transitive solvable-normal Sylow overgroups in M₂₂

A nontrivial solvable normal subgroup gives a nontrivial characteristic
abelian subgroup of the solvable radical, and then an elementary abelian
normal subgroup N. Under a transitive action on 22 points, its orbits have
a common prime-power size dividing 22. Faithfulness excludes size one,
so the only possibilities are two-point orbits for p = 2 or eleven-point
orbits for p = 11.

In the first case, Burnside's formula and the six fixed points of every
involution would give 11|N| = 22 + 6(|N| - 1), which has no integral solution.
In the second, Lagrange forces |N| = 11. Conjugation maps the overgroup to
the order-ten automorphism group of N. Since the overgroup's order is divisible
by four, its kernel contains an involution. Then N preserves that involution's
fixed hexad, contradicting the hexad stabilizer's order 5760.

This supplies the transitive exclusion in the geometric coverage needed for
Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973). All actions are inherited
from the actual degree-22 Mathieu permutations; normality is relative to X.
-/

public section

open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M22SolvableSylow

private theorem normal_pgroup_orbits (X : Subgroup M22) [IsPretransitive X (Fin 22)]
    (N : Subgroup X) [N.Normal] (hN : N ≠ ⊥) (p : ℕ) (hp : p.Prime)
    (hNp : IsPGroup p N) :
    (p = 2 ∧ ∀ a : Fin 22, (orbit N a).ncard = 2) ∨
      (p = 11 ∧ ∀ a : Fin 22, (orbit N a).ncard = 11) := by
  let : Fact p.Prime := ⟨hp⟩
  have heq (a b : Fin 22) : (orbit N a).ncard = (orbit N b).ncard := by
    obtain ⟨g, rfl⟩ := exists_smul_eq X a b
    rw [← smul_orbit_eq_orbit_smul, Set.ncard_smul_set]
  have hnotone (a : Fin 22) : (orbit N a).ncard ≠ 1 := by
    intro h1
    apply hN
    apply eq_bot_iff.mpr
    intro n hn
    have hn1 : (⟨n, hn⟩ : N) = 1 := by
      apply eq_of_smul_eq_smul (α := Fin 22)
      intro b
      have hb : (orbit N b).Subsingleton := Set.ncard_le_one_iff_subsingleton.mp
        (by rw [← heq a b, h1])
      simpa only [one_smul] using hb (mem_orbit b (⟨n, hn⟩ : N)) (mem_orbit_self b)
    exact congrArg Subtype.val hn1
  have hdiv : (orbit N (0 : Fin 22)).ncard ∣ 22 := by
    simpa using (IsBlock.orbit_of_normal (N := N) (0 : Fin 22)).ncard_dvd_card
      ⟨0, mem_orbit_self 0⟩
  have hposs : (orbit N (0 : Fin 22)).ncard ∈ ({1, 2, 11, 22} : Finset ℕ) := by
    have h := Nat.mem_divisors.mpr ⟨hdiv, (by decide : (22 : ℕ) ≠ 0)⟩
    simpa only [show (22 : ℕ).divisors = {1, 2, 11, 22} from by decide +kernel] using h
  obtain ⟨k, hk⟩ := hNp.card_orbit (0 : Fin 22)
  rw [Nat.card_coe_set_eq] at hk
  have hprime (q : ℕ) (hq : q.Prime) (hqdiv : q ∣ (orbit N (0 : Fin 22)).ncard) : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow (hk ▸ hqdiv))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hposs
  rcases hposs with h1 | h2 | h11 | h22
  · exact (hnotone 0 h1).elim
  · exact Or.inl ⟨(hprime 2 (by decide) (by rw [h2])).symm,
      fun a => (heq a 0).trans h2⟩
  · exact Or.inr ⟨(hprime 11 (by decide) (by rw [h11])).symm,
      fun a => (heq a 0).trans h11⟩
  · have h2 := hprime 2 (by decide) (by rw [h22]; decide)
    have h11 := hprime 11 (by decide) (by rw [h22]; decide)
    omega

private theorem no_binary_two_orbits (X : Subgroup M22) (N : Subgroup X)
    [IsElementaryAbelian 2 N] (horb : ∀ a : Fin 22, (orbit N a).ncard = 2) : False := by
  classical
  let : Fintype N := Fintype.ofFinite _
  let Ω := orbitRel.Quotient N (Fin 22)
  let : Fintype Ω := Fintype.ofFinite _
  have hsum := Nat.card_congr (selfEquivSigmaOrbits N (Fin 22))
  rw [Nat.card_sigma] at hsum
  have hΩ : Fintype.card Ω = 11 := by
    simp only [Nat.card_fin, Nat.card_coe_set_eq, horb, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] at hsum
    change 22 = Fintype.card Ω * 2 at hsum
    omega
  have hfix (n : N) (hn : n ≠ 1) : Fintype.card (fixedBy (Fin 22) n) = 6 := by
    have ht : orderOf (n.val.val : M22) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact orderOf_eq_prime ((Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 N)) n) hn
    obtain ⟨B, hB, hf⟩ := m22_exists_fixed_hexad n.val.val ht
    have he : fixedBy (Fin 22) n = (B : Set (Fin 22)) := Set.ext hf
    rw [Set.fintypeCard_eq_ncard, he, Set.ncard_coe_finset, m22Block_card B hB]
  have hb := sum_card_fixedBy_eq_card_orbits_mul_card_group N (Fin 22)
  have hsumfix : (∑ n : N, Fintype.card (fixedBy (Fin 22) n)) =
      22 + (Fintype.card N - 1) * 6 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : N))]
    have he : ∑ n ∈ Finset.univ.erase (1 : N), Fintype.card (fixedBy (Fin 22) n) =
        (Fintype.card N - 1) * 6 := by
      rw [Finset.sum_congr rfl (fun n hn => hfix n (Finset.mem_erase.mp hn).1)]
      simp
    rw [he, Set.fintypeCard_eq_ncard, fixedBy_one_eq_univ]
    simp [Nat.add_comm]
  rw [hsumfix, hΩ] at hb
  have hpos : 0 < Fintype.card N := Fintype.card_pos
  omega

private theorem no_normal_eleven (X : Subgroup M22) (N : Subgroup X)
    [N.Normal] (hcN : Nat.card N = 11) (h4 : 4 ∣ Nat.card X) : False := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let : IsCyclic N := isCyclic_of_prime_card hcN
  let f : X →* MulAut N := MulAut.conjNormal
  have hAut : Nat.card (MulAut N) = 10 := by
    rw [IsCyclic.card_mulAut, hcN]
    decide
  have hr : Nat.card f.range ∣ 10 := hAut ▸ card_subgroup_dvd_card f.range
  have hm : Nat.card f.ker * Nat.card f.range = Nat.card X := by
    rw [← index_ker, Subgroup.card_mul_index]
  have hd : 4 ∣ Nat.card f.ker * 10 := h4.trans
    (hm ▸ Nat.mul_dvd_mul_left (Nat.card f.ker) hr)
  have heven : 2 ∣ Nat.card f.ker := by omega
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2 heven
  have htM : orderOf (t.val.val : M22) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact ht
  have hle : N.map X.subtype ≤ stabilizer M22 (m22FixedPoints t.val.val) := by
    rintro n ⟨n', hn', rfl⟩
    apply m22_centralizer_le_fixedPoints_stabilizer
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg (fun a : MulAut N => (a ⟨n', hn'⟩).val)
      (MonoidHom.mem_ker.mp t.property)
    change t.val * n' * t.val⁻¹ = n' at he
    have he' : t.val * n' = n' * t.val := (mul_inv_eq_iff_eq_mul).mp he
    exact (congrArg Subtype.val he').symm
  have hdN := card_dvd_of_le hle
  rw [card_map_of_injective X.subtype_injective, hcN,
    m22Hexad_stabilizer_card (m22FixedPoints_mem_blocks _ htM)] at hdN
  norm_num at hdN


private theorem elementary_seed (X D : Subgroup M22) (hle : D ≤ X)
    (hn : (D.subgroupOf X).Normal) (hs : Group.IsSolvable D) (hthree : 3 ∣ Nat.card D) :
    ∃ p : ℕ, p.Prime ∧ ∃ E : Subgroup X, E.Normal ∧ IsElementaryAbelian p E ∧ E ≠ ⊥ := by
  let := hs
  let DX := D.subgroupOf X
  have hDXsol : Group.IsSolvable DX := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hle).toMonoidHom) (subgroupOfEquivOfLe hle).injective
  have hDXne : DX ≠ ⊥ := by
    intro he
    have hc : Nat.card DX = Nat.card D := Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
    rw [he, Subgroup.card_bot] at hc
    rw [← hc] at hthree
    norm_num at hthree
  have hrad : solvableRadical X ≠ ⊥ := by
    intro he
    exact hDXne (le_bot_iff.mp (he ▸ le_solvableRadical DX hn hDXsol))
  obtain ⟨A, hAc, hAa, hA⟩ := exists_abelian_characteristic_of_solvableRadical_ne_bot hrad
  let := hAc
  let := hAa
  obtain ⟨p, hp, E, _, hEc, hEe, hE⟩ := A.exists_elementaryAbelian_characteristic_le hA
  let := hEc
  exact ⟨p, hp, E, inferInstance, hEe, hE⟩


private theorem eleven_pgroup_card (X : Subgroup M22) (N : Subgroup X)
    (hN : N ≠ ⊥) (hp : IsPGroup 11 N) : Nat.card N = 11 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hd : 11 ^ k ∣ 443520 := by
    rw [← hk, ← m22_order]
    exact (card_subgroup_dvd_card N).trans (card_subgroup_dvd_card X)
  have hlt : k < 2 := by
    by_contra! hn
    have hd' : 121 ∣ 443520 := (pow_dvd_pow 11 hn).trans hd
    norm_num at hd'
  have hpos : 1 < 11 ^ k := hk ▸ (Subgroup.one_lt_card_iff_ne_bot N).mpr hN
  have hk1 : k = 1 := by
    interval_cases k <;> norm_num at *
  simpa only [hk1, pow_one] using hk

/-- A nontrivial solvable normal seed prevents a Sylow overgroup from acting transitively. -/
theorem not_pretransitive_of_solvable_normal_three (X D : Subgroup M22) (hle : D ≤ X)
    (hn : (D.subgroupOf X).Normal) (hs : Group.IsSolvable D) (hthree : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    ¬ IsPretransitive X (Fin 22) := by
  intro ht
  let := ht
  obtain ⟨p, hp, N, hNn, hNe, hN⟩ := elementary_seed X D hle hn hs hthree
  let := hNn
  let := hNe
  have hNp := IsElementaryAbelian.isPGroup p N
  rcases normal_pgroup_orbits X N hN p hp hNp with ⟨rfl, horb⟩ | ⟨rfl, _⟩
  · exact no_binary_two_orbits X N horb
  · obtain ⟨U, hU⟩ := hU
    have h4 : 4 ∣ Nat.card X :=
      (U.pow_dvd_card_of_pow_dvd_card (n := 2) (by rw [m22_order]; decide)).trans
        (card_dvd_of_le hU)
    exact no_normal_eleven X N (eleven_pgroup_card X N hN hNp) h4

end Sporadic.Mathieu.M22SolvableSylow
