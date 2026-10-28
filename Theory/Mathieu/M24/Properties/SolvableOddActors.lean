module
public import Theory.Mathieu.M24.Properties.QuinticSylowOvergroups
public import Theory.Mathieu.M24.Properties.CubicExponent
public import Theory.GroupTheory.Hall.Existence
public import Mathlib.Algebra.Group.PUnit

/-!
# Odd actors in solvable M₂₄ Sylow overgroups

Hall existence places the supplied Sylow two-subgroup inside a Hall
three-complement. Native octad geometry makes that complement a two-group,
so only two and three divide the solvable overgroup order. The native
exponent-three Sylow calculation then bounds every cyclic odd actor by three.
The same bound lifts through any two-group kernel, which is disjoint from
the odd actor. This retains the actual actor in the J₄ Mathieu local row.

Source: Aschbacher--Smith 5.1.13, printed p.637; the native M₂₄ geometry
and Sylow certificates in the imported modules (GLS3, Table 5.3e).
-/

public section
open Subgroup
namespace Sporadic.Mathieu.M24SolvableActors

/-- A solvable overgroup of a full M₂₄ Sylow involves only primes two and three. -/
theorem prime_dvd_card (S : Sylow 2 M24) (K : Subgroup M24)
    (hSK : (S : Subgroup M24) ≤ K) (hs : Group.IsSolvable K)
    (p : ℕ) (hp : p.Prime) (hpk : p ∣ Nat.card K) : p = 2 ∨ p = 3 := by
  classical
  let _ : MulDistribMulAction Unit K := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  let P := S.subtype hSK
  let π : Set Nat.Primes := {q | q.val ≠ 3}
  have hPπ : IsPiSubgroup π (P : Subgroup K) := by
    intro q hq
    obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
    have hq2 := Nat.prime_eq_prime_of_dvd_pow q.property Nat.prime_two (hn ▸ hq)
    change q.val ≠ 3
    omega
  obtain ⟨U,hU,_,hPU⟩ := exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (A := Unit) hs (by simp) π (P : Subgroup K) hPπ ⟨fun _ _ => Iff.rfl⟩
  have hUS : (S : Subgroup M24) ≤ U.map K.subtype := by
    have hh := map_mono (f := K.subtype) hPU
    simpa only [P,Sylow.coe_subtype,map_subgroupOf_eq_of_le hSK] using hh
  have h3 : ¬ 3 ∣ Nat.card U := fun h => hU.p_in_pi_of_p_dvd_card ⟨3,Nat.prime_three⟩ h rfl
  have hUc : Nat.card U = 1024 := by
    have hh := M24QuinticSylow.card_eq_1024 S (U.map K.subtype) hUS
      (by rwa [card_map_of_injective K.subtype_injective])
    rwa [card_map_of_injective K.subtype_injective] at hh
  by_cases hp3 : p = 3
  · exact Or.inr hp3
  left
  have hi : ¬ p ∣ U.index := fun hi => hU.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hi hp3
  have hpc : p ∣ Nat.card U := (hp.dvd_mul.mp (U.card_mul_index.symm ▸ hpk)).resolve_right hi
  rw [hUc] at hpc
  exact Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two (show p ∣ 2^10 from hpc)

/-- Every odd subgroup of that same overgroup is a three-group. -/
theorem odd_isPGroup (S : Sylow 2 M24) (K D : Subgroup M24)
    (hSK : (S : Subgroup M24) ≤ K) (hs : Group.IsSolvable K)
    (hDK : D ≤ K) (hodd : Odd (Nat.card D)) : IsPGroup 3 D := by
  have he := Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := D)).ne' (by
    intro p hp hpd
    rcases prime_dvd_card S K hSK hs p hp (hpd.trans (card_dvd_of_le hDK)) with h | h
    · subst p
      exact (hodd.not_two_dvd_nat hpd).elim
    · exact h)
  exact IsPGroup.of_card he

/-- The actual cyclic odd actor has order dividing three. -/
theorem cyclic_odd_card_dvd_three (S : Sylow 2 M24) (K D : Subgroup M24)
    (hSK : (S : Subgroup M24) ≤ K) (hs : Group.IsSolvable K)
    (hDK : D ≤ K) (hodd : Odd (Nat.card D)) (hcyc : IsCyclic D) : Nat.card D ∣ 3 := by
  let := hcyc
  obtain ⟨d,hd⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := D)
  have hnine : ¬ 9 ∣ Nat.card D := by
    simpa only [orderOf_coe,hd] using m24_not_nine_dvd_orderOf (d : M24)
  obtain ⟨n,hn⟩ := (odd_isPGroup S K D hSK hs hDK hodd).exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra hh
    exact hnine (hn ▸ pow_dvd_pow 3 (by omega : 2 ≤ n))
  rw [hn]
  exact pow_dvd_pow 3 hnle

private theorem odd_map_card {X Y : Type*} [Group X] [Finite X] [Group Y]
    (f : X →* Y) (hk : IsPGroup 2 f.ker) (D : Subgroup X) (hodd : Odd (Nat.card D)) :
    Nat.card (D.map f) = Nat.card D := by
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hd : Disjoint D f.ker := disjoint_of_coprime_natCard (by
    rw [hn]
    exact hodd.coprime_two_right.pow_right n)
  have hi : Function.Injective (f.comp D.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (hd.le_bot ⟨x.property,hx⟩)
  let e : D ≃* D.map f := MulEquiv.ofBijective (f.subgroupMap D)
    ⟨fun x y hh => hi (congrArg Subtype.val hh),f.subgroupMap_surjective D⟩
  exact (Nat.card_congr e.toEquiv).symm

/-- The actor order bound survives a literal quotient with two-group kernel. -/
theorem cyclic_odd_card_dvd_three_of_two_kernel {X : Type*} [Group X] [Finite X]
    (f : X →* M24) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 X) (K D : Subgroup X)
    (hSK : (S : Subgroup X) ≤ K) (hs : Group.IsSolvable K)
    (hDK : D ≤ K) (hodd : Odd (Nat.card D)) (hcyc : IsCyclic D) : Nat.card D ∣ 3 := by
  let := hs
  let := hcyc
  have hs' : Group.IsSolvable (K.map f) := Group.isSolvable_of_surjective
    (f := f.subgroupMap K) (f.subgroupMap_surjective K)
  have hc := odd_map_card f hk D hodd
  have hd := cyclic_odd_card_dvd_three (S.mapSurjective hf) (K.map f) (D.map f)
    (map_mono hSK) hs' (map_mono hDK) (hc ▸ hodd) (isCyclic_of_surjective
      (f.subgroupMap D) (f.subgroupMap_surjective D))
  rwa [hc] at hd

end Sporadic.Mathieu.M24SolvableActors
