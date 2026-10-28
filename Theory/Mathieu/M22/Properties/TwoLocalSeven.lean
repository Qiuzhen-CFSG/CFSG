module
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Coverage
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.LocalClassification.NativeOrders
public import Theory.GroupTheory.SylowContainingTwoLocal

/-!
# Seven-free two-local Sylow overgroups in M₂₂

A nontrivial normal elementary two-subgroup of a transitive degree-22
subgroup would have eleven two-point orbits. Burnside's formula and the
six fixed points of every involution rule this out. Geometric Sylow
overgroup coverage then puts the subgroup in a pair or hexad stabilizer,
whose orders are prime to seven. Passing to a maximal two-local supplies
the required normal elementary subgroup.

The two orbit arguments reuse the private proofs in
`SolvableSylowOvergroups.Coverage.Transitive` without changing that shared
module's public boundary. All actions are the actual M₂₂ permutations.
The point-control application excludes M₂₂ for the original L₃(2) quotient
in Aschbacher--Smith 10.2.9, printed p.750, using A.3.12, pp.47--48.
-/

public section
open Subgroup MulAction Theory.GroupTheory
open scoped Pointwise
namespace Sporadic.Mathieu.M22TwoLocalOrders

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

/-- A nontrivial normal elementary two-subgroup excludes transitivity in degree 22. -/
theorem not_pretransitive_of_normal_elementary (X : Subgroup M22) (E : Subgroup X)
    [E.Normal] [IsElementaryAbelian 2 E] (hne : E ≠ ⊥) :
    ¬ IsPretransitive X (Fin 22) := by
  intro htrans
  let := htrans
  rcases normal_pgroup_orbits X E hne 2 Nat.prime_two
    (IsElementaryAbelian.isPGroup 2 E) with ⟨_,horb⟩ | ⟨h,_⟩
  · exact no_binary_two_orbits X E horb
  · omega

/-- A Sylow overgroup with a nontrivial normal elementary two-subgroup is seven-free. -/
theorem not_seven_dvd_card_of_normal_elementary (S : Sylow 2 M22)
    (X : Subgroup M22) (hSX : (S : Subgroup M22) ≤ X)
    (E : Subgroup X) [E.Normal] [IsElementaryAbelian 2 E] (hne : E ≠ ⊥) :
    ¬ 7 ∣ Nat.card X := by
  rcases M22SolvableSylow.coverage_of_not_pretransitive X ⟨S,hSX⟩
    (not_pretransitive_of_normal_elementary X E hne) with ⟨B,hB,hXB⟩ | ⟨B,hB,hXB⟩
  · intro hd
    have h := hd.trans (card_dvd_of_le hXB)
    rw [m22Hexad_stabilizer_card hB] at h
    norm_num at h
  · obtain ⟨g,hg⟩ := M22SolvableSylow.LocalClassification.exists_smul_pair_eq_standard hB
    have hmap := map_mono (f := (MulAut.conj g).toMonoidHom) hXB
    rw [← stabilizer_smul_eq_stabilizer_map_conj g B,hg] at hmap
    intro hd
    have hd' : 7 ∣ Nat.card (X.map (MulAut.conj g).toMonoidHom) := by
      rwa [card_map_of_injective (MulAut.conj g).injective]
    have h := hd'.trans (card_dvd_of_le hmap)
    change 7 ∣ Nat.card m22PairStabilizer at h
    rw [m22PairStabilizer_card] at h
    norm_num at h

/-- Every two-local containing a full Sylow subgroup of M₂₂ is seven-free. -/
theorem not_seven_dvd_card_twoLocal (S : Sylow 2 M22) (X : Subgroup M22)
    (hX : IsTwoLocal X) (hSX : (S : Subgroup M22) ≤ X) : ¬ 7 ∣ Nat.card X := by
  obtain ⟨Y,hXY,hY⟩ := Finite.exists_le_maximal hX
  obtain ⟨A,hA,hEA,hYA⟩ := exists_elementary_normalizer_of_isMaximalTwoLocal hY
  let := hEA
  have hAY : A ≤ Y := hYA.symm ▸ A.le_normalizer
  let E := A.subgroupOf Y
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hAY).mpr (hYA ▸ le_rfl)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hAY
  have hE : E ≠ ⊥ := by
    intro h
    apply hA
    rw [← map_subgroupOf_eq_of_le hAY,show A.subgroupOf Y = E from rfl,h,Subgroup.map_bot]
  exact fun hd => not_seven_dvd_card_of_normal_elementary S Y (hSX.trans hXY) E hE
    (hd.trans (card_dvd_of_le hXY))

end Sporadic.Mathieu.M22TwoLocalOrders
