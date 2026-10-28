module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Holomorph
public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.Frattini.BinarySquares

/-!
# Rank-one subgroups of the cyclic-eight holomorph

A subgroup of C₈ ⋊ (Z/8)ˣ with two-rank one and nontrivial Frattini
subgroup is cyclic of order four or eight, or quaternion of order eight.
No normality assumption is needed. The finite two-group rank-one theorem
reduces to cyclic and generalized quaternion groups. The model has exponent
eight, and its explicit multiplication also excludes quaternion order sixteen.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 2.5.27, printed p.569. This proves the intrinsic subgroup calculation;
transport to a Sylow subgroup of Aut(A₆) is a separate step.
-/

open Subgroup
open scoped IsMulCommutative
namespace AlternatingSix.ShadowLocal.Holomorph

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem eighth_power (x : Model) : x ^ 8 = 1 := by
  revert x
  decide +kernel

private theorem quaternion_sixteen_relation (a b : Model)
    (hsq : b ^ 2 = a ^ 4) (hinv : b * a = a⁻¹ * b) : a ^ 4 = 1 := by
  revert a b
  decide +kernel

private theorem two_group : IsPGroup 2 Model :=
  IsPGroup.of_card (by simpa using card_model : Nat.card Model = 2 ^ 5)

private theorem no_elementary_four (X : Subgroup Model) (hrank : primeRank 2 X = 1)
    (E : Subgroup X) (hE : IsElementaryAbelian 2 E) : Nat.card E ≠ 4 := by
  let := hE
  let : CommGroup E := IsMulCommutative.instCommGroup
  intro hcard
  have h := primeRank_ge_of_elementary_embedding
    (p := 2) (e := 2)
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E))
    (by simpa using hcard) E.subtype E.subtype_injective
  omega

private theorem cyclic_card (X : Subgroup Model) [IsCyclic X]
    (hphi : frattini X ≠ ⊥) : Nat.card X = 4 ∨ Nat.card X = 8 := by
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := X)
  have hd : Nat.card X ∣ 8 := by
    rw [← hx, ← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one (eighth_power x)
  have hnot (hsmall : Nat.card X ∣ 2) : False := by
    apply hphi
    rw [(two_group.to_subgroup X).frattini_eq_closure_squares]
    apply eq_bot_iff.mpr
    apply (closure_le _).mpr
    rintro _ ⟨y, rfl⟩
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard y).trans hsmall)
  have hcases : Nat.card X = 1 ∨ Nat.card X = 2 ∨ Nat.card X = 4 ∨ Nat.card X = 8 := by
    obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card X ∣ 2 ^ 3 from hd)
    interval_cases k <;> simp_all
  rcases hcases with h | h | h | h
  · exact (hnot (by simp [h])).elim
  · exact (hnot (by simp [h])).elim
  · exact Or.inl h
  · exact Or.inr h

private theorem quaternion_parameter (X : Subgroup Model) (n : ℕ) (hn : 3 ≤ n)
    (e : X ≃* QuaternionGroup (2 ^ (n - 2))) : n = 3 := by
  have hc : 4 * 2 ^ (n - 2) ≤ 32 := by
    have := X.card_le_card_group
    rw [card_model, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card] at this
    exact this
  have hnle : n ≤ 5 := by
    by_contra h
    have hp : 2 ^ 4 ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hp
    omega
  interval_cases n
  · rfl
  · let f : QuaternionGroup 4 →* Model := X.subtype.comp e.symm.toMonoidHom
    have hf : Function.Injective f := X.subtype_injective.comp e.symm.injective
    have hs : f (QuaternionGroup.xa 0) ^ 2 = f (QuaternionGroup.a 1) ^ 4 := by
      rw [← map_pow, ← map_pow]
      congr 1
    have hi : f (QuaternionGroup.xa 0) * f (QuaternionGroup.a 1) =
        (f (QuaternionGroup.a 1))⁻¹ * f (QuaternionGroup.xa 0) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    have h := quaternion_sixteen_relation _ _ hs hi
    rw [← map_pow, ← f.map_one] at h
    have hn : (QuaternionGroup.a 1 : QuaternionGroup 4) ^ 4 ≠ 1 := by decide +kernel
    exact (hn (hf h)).elim
  · let f : QuaternionGroup 8 →* Model := X.subtype.comp e.symm.toMonoidHom
    have hf : Function.Injective f := X.subtype_injective.comp e.symm.injective
    have h := eighth_power (f (QuaternionGroup.a 1))
    rw [← map_pow, ← f.map_one] at h
    have hn : (QuaternionGroup.a 1 : QuaternionGroup 8) ^ 8 ≠ 1 := by decide +kernel
    exact (hn (hf h)).elim

/-- The rank-one subgroups with nontrivial Frattini subgroup are C4, C8, or Q8. -/
public theorem rank_one_subgroup_classification (X : Subgroup Model)
    (hrank : primeRank 2 X = 1) (hphi : frattini X ≠ ⊥) :
    Nonempty (X ≃* Multiplicative (ZMod 4)) ∨
    Nonempty (X ≃* Multiplicative (ZMod 8)) ∨
    Nonempty (X ≃* QuaternionGroup 2) := by
  rcases (two_group.to_subgroup X).isCyclic_or_quaternion_of_no_elementary_four
      (no_elementary_four X hrank) with hcyclic | ⟨n, hn, ⟨e⟩⟩
  · let := hcyclic
    rcases cyclic_card X hphi with h | h
    · exact Or.inl ⟨mulEquivOfCyclicCardEq (by simpa using h)⟩
    · exact Or.inr (Or.inl ⟨mulEquivOfCyclicCardEq (by simpa using h)⟩)
  · have h := quaternion_parameter X n hn e
    subst n
    exact Or.inr (Or.inr ⟨e⟩)

end AlternatingSix.ShadowLocal.Holomorph
