module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.Automorphisms
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.Quasithin.Rank

/-!
# Cubic automorphism subgroups from their inner and outer images

Three-rank at most one makes the Sylow three-subgroups cyclic. Thus a
cubic subgroup in the inner automorphism group has order dividing three.
If its outer image also has order dividing three, the whole subgroup has
order dividing nine and is abelian. A cyclic subgroup containing all outer
squares suffices: for a cubic element, its fourth power is itself.

This is the group-theoretic reduction behind the odd-model inspection on
Aschbacher--Smith, combined manuscript, printed p.1137 (PDF p.1154).
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne

private theorem cubic_card_dvd_three {G : Type*} [Group G] [Finite G]
    (hr : primeRank 3 G ≤ 1) (hpow : ∀ g : G, g ^ 3 = 1) : Nat.card G ∣ 3 := by
  have hp : IsPGroup 3 G := fun g => ⟨1, by simpa using hpow g⟩
  let P : Sylow 3 G := (hp.to_subgroup ⊤).toSylow (by simp)
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  let : IsCyclic G := isCyclic_of_surjective (P : Subgroup G).subtype (by
    intro g
    exact ⟨⟨g, by trivial⟩, rfl⟩)
  rw [← IsCyclic.exponent_eq_card]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow

private theorem cubic_of_outer_card {S : Type*} [Group S] [Finite S]
    (hr : primeRank 3 S ≤ 1)
    (ho : ∀ B : Subgroup (MulAut.Outer S), (∀ b : B, b ^ 3 = 1) → Nat.card B ∣ 3) :
    CubicAutomorphismsAbelian S := by
  intro A hA
  let P : Sylow 3 S := Classical.choice inferInstance
  have hi : primeRank 3 (MulAut.innerSubgroup S) ≤ 1 :=
    P.primeRank_le_one_of_surjective
      (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr)
      MulAut.conj.rangeRestrict MulAut.conj.rangeRestrict_surjective
  let f : A →* MulAut.Outer S := (QuotientGroup.mk' (MulAut.innerSubgroup S)).comp A.subtype
  let k : f.ker →* MulAut.innerSubgroup S :=
    { toFun := fun x => ⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : MulAut.innerSubgroup S => x.val) h
  have hkc : Nat.card f.ker ∣ 3 := cubic_card_dvd_three
    ((primeRank_le_of_injective 3 k hk).trans hi) (fun x => Subtype.ext (hA x.val))
  have hrc : Nat.card f.range ∣ 3 := ho f.range (by
    rintro ⟨x, a, rfl⟩
    apply Subtype.ext
    exact (map_pow f a 3).symm.trans ((congrArg f (hA a)).trans f.map_one))
  have hc : Nat.card A ∣ 3 ^ 2 := by
    rw [← f.ker.card_mul_index, index_ker]
    exact Nat.mul_dvd_mul hkc hrc
  obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hc
  interval_cases n
  · let : Subsingleton A := (Nat.card_eq_one_iff_unique.mp (by simpa using hc)).1
    infer_instance
  · let : IsCyclic A := isCyclic_of_card_dvd_prime (p := 3) (by simpa using hc.dvd)
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hc

/-- Three-rank at most one in both the group and its actual outer quotient
forces every cubic automorphism subgroup to be abelian. -/
theorem cubic_of_outer_rank_le_one {S : Type*} [Group S] [Finite S]
    (hr : primeRank 3 S ≤ 1) (ho : primeRank 3 (MulAut.Outer S) ≤ 1) :
    CubicAutomorphismsAbelian S :=
  cubic_of_outer_card hr fun B hB => cubic_card_dvd_three
    ((primeRank_le_of_injective 3 B.subtype B.subtype_injective).trans ho) hB

/-- A cyclic subgroup containing every outer square controls every cubic image. -/
theorem cubic_of_outer_squares {S : Type*} [Group S] [Finite S]
    (hr : primeRank 3 S ≤ 1) (D : Subgroup (MulAut.Outer S)) (hD : IsCyclic D)
    (hsq : ∀ a : MulAut S,
      (QuotientGroup.mk' (MulAut.innerSubgroup S) a) ^ 2 ∈ D) :
    CubicAutomorphismsAbelian S := by
  apply cubic_of_outer_card hr
  intro B hB
  have hle : B ≤ D := by
    intro b hb
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup S) b
    have hc := congrArg Subtype.val (hB ⟨_, hb⟩)
    change (QuotientGroup.mk' (MulAut.innerSubgroup S) a) ^ 3 = 1 at hc
    have he : ((QuotientGroup.mk' (MulAut.innerSubgroup S) a) ^ 2) ^ 2 =
        QuotientGroup.mk' (MulAut.innerSubgroup S) a := by
      rw [← pow_mul]
      change _ ^ (3 + 1) = _
      rw [pow_succ, hc, one_mul]
    exact he ▸ D.pow_mem (hsq a) 2
  let := hD
  let : IsCyclic B := Subgroup.isCyclic_of_le hle
  rw [← IsCyclic.exponent_eq_card]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hB

/-- Transport the intrinsic property along an actual model isomorphism. -/
theorem cubic_of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (hT : CubicAutomorphismsAbelian T) : CubicAutomorphismsAbelian S := by
  intro A hA
  let f := (MulAut.congr e).toMonoidHom
  let B := A.map f
  let := hT B (by
    rintro ⟨b, a, ha, rfl⟩
    apply Subtype.ext
    exact (map_pow f a 3).symm.trans
      ((congrArg f (congrArg Subtype.val (hA ⟨a, ha⟩))).trans f.map_one))
  let g := f.subgroupMap A
  have hg : Function.Injective g := fun x y h =>
    Subtype.ext ((MulAut.congr e).injective (congrArg Subtype.val h))
  exact IsMulCommutative.of_comm fun a b => hg (by simp only [map_mul, mul_comm])

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
