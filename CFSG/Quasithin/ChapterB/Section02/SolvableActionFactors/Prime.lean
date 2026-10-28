module
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors
public import Theory.GroupTheory.ReducedNormal.SylowSupplement
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
/-!
# The odd chief prime in solvable Thompson factorization

For a normal subgroup K with p-group quotient by its two-core, a Sylow
two-supplement makes the ambient group solvable. Noncentral Thompson action
on R2 supplies an actual SL2(2) factor in the faithful reduced action, so
three divides the ambient order. Both two-group sections have order prime
to three; hence three divides the p-group K/O2(K), forcing p=3.

Source: Aschbacher--Smith B.2.16, used in 13.7.4(1), printed p.937.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- The prime of the normal odd chief actor is three when its Sylow
supplement moves the actual reduced module. -/
theorem prime_eq_three_of_reduced_sylow_movement
    (p : ℕ) [Fact p.Prime] (K : Subgroup G) [K.Normal]
    (hK : IsPGroup p (K ⧸ pCore 2 K)) (S : Sylow 2 G)
    (hgen : K ⊔ (S : Subgroup G) = ⊤)
    (hc : centralizer (reducedTwoSubgroup G : Set G) = pCore 2 G)
    (hJ : ¬ elementaryAbelianMaxJ (S : Subgroup G) ≤
      centralizer (reducedTwoSubgroup G : Set G)) : p = 3 := by
  let U := reducedTwoSubgroup G
  let : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
  let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
  let : Group.IsNilpotent (K ⧸ pCore 2 K) := hK.isNilpotent
  let : Group.IsSolvable K := (Group.isSolvable_iff_subgroup_quotient (pCore 2 K)).mpr
    ⟨inferInstance,inferInstance⟩
  have hQ : IsPGroup 2 (G ⧸ K) := isPGroup_quotient_of_sup_eq_top K S S.isPGroup' hgen
  let : Group.IsNilpotent (G ⧸ K) := hQ.isNilpotent
  let : Group.IsSolvable G := (Group.isSolvable_iff_subgroup_quotient K).mpr
    ⟨inferInstance,inferInstance⟩
  let q := QuotientGroup.mk' (pCore 2 G)
  have hker : q.ker = centralizer (U : Set G) := (QuotientGroup.ker_mk' _).trans hc.symm
  obtain ⟨d, _, _, _, _⟩ := thompson_factors_of_solvable_action U q
    (QuotientGroup.mk'_surjective _) hker S hJ inferInstance (pCore_quotient_pCore_eq_bot 2)
  let i : Fin d.count := ⟨0,d.count_pos⟩
  have hfactor : Nat.card (d.factor i) = 6 := by
    have he := (d.factorModel i).trans (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)
    rw [Nat.card_congr he.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have h3 : 3 ∣ Nat.card G := by
    apply dvd_trans ?_ (Subgroup.card_quotient_dvd_card (pCore 2 G))
    exact (show 3 ∣ Nat.card (d.factor i) by rw [hfactor]; decide).trans
      (card_subgroup_dvd_card (d.factor i))
  have h3K : 3 ∣ Nat.card K := by
    rw [card_eq_card_quotient_mul_card_subgroup K] at h3
    obtain ⟨n, hn⟩ := hQ.exists_card_eq
    apply (Nat.prime_three.dvd_mul.mp h3).resolve_left
    rw [hn]
    intro hh
    have hnot : ¬ 3 ∣ 2 := by decide
    exact hnot (Nat.prime_three.dvd_of_dvd_pow hh)
  have h3Q : 3 ∣ Nat.card (K ⧸ pCore 2 K) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 K)] at h3K
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    apply (Nat.prime_three.dvd_mul.mp h3K).resolve_right
    rw [hn]
    intro hh
    have hnot : ¬ 3 ∣ 2 := by decide
    exact hnot (Nat.prime_three.dvd_of_dvd_pow hh)
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  rw [hn] at h3Q
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).mp
    (Nat.prime_three.dvd_of_dvd_pow h3Q)).symm

end CFSG.Quasithin.ChapterB
