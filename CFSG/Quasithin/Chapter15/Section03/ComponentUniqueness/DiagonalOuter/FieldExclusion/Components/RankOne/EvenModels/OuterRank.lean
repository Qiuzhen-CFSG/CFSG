module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.Automorphisms
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.SolvableOuterQuotient


/-!
# Cubic automorphism subgroups from inner and outer three-ranks

At an odd prime, rank at most one forces cyclic Sylow subgroups. Apply this
first to S and its actual inner automorphism image, then to Aut(S)/Inn(S).
An exponent-three subgroup A has cyclic kernel and image in the outer
quotient, both of order dividing three. Thus |A| divides nine and A is abelian.
No simplicity, standard-automorphism coverage, or model classification is
assumed in this reduction.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, the
three-rank-one automorphism inspection in the proof of 15.3.38, printed p.1137.
The model-specific outer-rank premises are discharged in the consumers.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

private theorem cubic_card_dvd_three {G : Type*} [Group G] [Finite G]
    (hr : primeRank 3 G ≤ 1) (he : ∀ g : G, g ^ 3 = 1) : Nat.card G ∣ 3 := by
  have hp : IsPGroup 3 G := fun g => ⟨1, by simpa using he g⟩
  have htop : IsPGroup 3 (⊤ : Subgroup G) := hp.to_subgroup ⊤
  obtain ⟨P, hP⟩ := htop.exists_le_sylow
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  have ht : (P : Subgroup G) = ⊤ := top_unique hP
  have hc : IsCyclic (⊤ : Subgroup G) := ht ▸ (inferInstance : IsCyclic P)
  let : IsCyclic G := Subgroup.topEquiv.isCyclic.mp hc
  rw [← IsCyclic.exponent_eq_card]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one he

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne

/-- The genuine inner and outer quotients reduce the cubic automorphism
property to two ordinary three-rank bounds. -/
theorem cubic_of_outer_three_rank_le_one {S : Type*} [Group S] [Finite S]
    (hr : primeRank 3 S ≤ 1) (ho : primeRank 3 (MulAut.Outer S) ≤ 1) :
    CubicAutomorphismsAbelian S := by
  intro A hA
  let I := MulAut.innerSubgroup S
  let q : A →* MulAut.Outer S := (QuotientGroup.mk' I).comp A.subtype
  have hI : primeRank 3 I ≤ 1 := by
    let P : Sylow 3 S := Classical.choice inferInstance
    exact P.primeRank_le_one_of_surjective
      (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr)
      MulAut.conj.rangeRestrict MulAut.conj.rangeRestrict_surjective
  let j : q.ker →* I :=
    { toFun x := ⟨x.val.val, by
        exact (QuotientGroup.eq_one_iff _).mp x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hj : Function.Injective j := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : I => z.val) h))
  have hk : Nat.card q.ker ∣ 3 := cubic_card_dvd_three
    ((primeRank_le_of_injective 3 j hj).trans hI) (fun x =>
      Subtype.ext (hA x.val))
  have him : Nat.card q.range ∣ 3 := by
    apply cubic_card_dvd_three
      ((primeRank_le_of_injective 3 q.range.subtype q.range.subtype_injective).trans ho)
    rintro ⟨x, a, rfl⟩
    apply Subtype.ext
    exact (map_pow q a 3).symm.trans ((congrArg q (hA a)).trans q.map_one)
  have hc : Nat.card A ∣ 3 ^ 2 := by
    have hcard : Nat.card A = Nat.card q.range * Nat.card q.ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange q).toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup q.ker
    rw [hcard, pow_two]
    exact Nat.mul_dvd_mul him hk
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hc
  interval_cases k
  · have hdiv : Nat.card A ∣ 3 := by rw [hcard]; norm_num
    let : IsCyclic A := isCyclic_of_card_dvd_prime hdiv
    infer_instance
  · let : IsCyclic A := isCyclic_of_prime_card (by simpa using hcard : Nat.card A = 3)
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard

/-- A cyclic actual outer group supplies the outer-rank premise. -/
theorem cubic_of_cyclic_outer {S : Type*} [Group S] [Finite S]
    (hr : primeRank 3 S ≤ 1) (ho : IsCyclic (MulAut.Outer S)) :
    CubicAutomorphismsAbelian S := by
  let := ho
  let P : Sylow 3 (MulAut.Outer S) := Classical.choice inferInstance
  exact cubic_of_outer_three_rank_le_one hr (P.primeRank_le_one_of_isCyclic inferInstance)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
