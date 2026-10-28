module
public import Theory.Quasithin.CentralThreeLocalRank

/-!
# Adding a central cubic element in a two-local subgroup

An elementary nine faithful modulo the ambient center combines with any
central element of order three. Cauchy's theorem only requires that three
divide the center's order; no primary-center assumption is needed.
Source: Aschbacher–Smith A.2.19, printed p.41.
-/
public section
namespace Theory.Quasithin

/-- An elementary subgroup independent of a center whose order is divisible by three
gains one rank inside any normalizer containing it. -/
theorem three_le_primeRank_normalizer_of_three_dvd_center
    {G A : Type*} [Group G] [Finite G] [CommGroup A] [Finite A]
    (hd : 3 ∣ Nat.card (Subgroup.center G))
    (Q : Subgroup G) (f : A →* G)
    (hf : Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp f))
    (hn : ∀ a, f a ∈ Subgroup.normalizer (Q : Set G))
    (ha : ∀ a : A, a ^ 3 = 1) (hc : Nat.card A = 3 ^ 2) :
    3 ≤ primeRank 3 (Subgroup.normalizer (Q : Set G)) := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) 3 hd
  let C := Subgroup.zpowers z
  let : CommGroup C := IsCyclic.commGroup
  have hC : Nat.card C = 3 := (Nat.card_zpowers z).trans hz
  let c : C →* G := (Subgroup.center G).subtype.comp C.subtype
  have hcz (x : C) : c x ∈ Subgroup.center G := x.val.property
  let F : C × A →* G :=
    { toFun := fun x => c x.1 * f x.2
      map_one' := by simp
      map_mul' := by
        intro x y
        change c (x.1 * y.1) * f (x.2 * y.2) = _
        rw [map_mul, map_mul]
        have hcomm : Commute (c y.1) (f x.2) :=
          (Subgroup.mem_center_iff.mp (hcz y.1) (f x.2)).symm
        exact hcomm.mul_mul_mul_comm _ _ }
  let q := QuotientGroup.mk' (Subgroup.center G)
  have hq (x : C) : q (c x) = 1 := (QuotientGroup.eq_one_iff _).mpr (hcz x)
  have hF : Function.Injective F := by
    intro x y h
    have hxy : x.2 = y.2 := by
      apply hf
      have hh := congrArg q h
      change q (c x.1 * f x.2) = q (c y.1 * f y.2) at hh
      change q (f x.2) = q (f y.2)
      simpa only [map_mul, hq, one_mul] using hh
    apply Prod.ext _ hxy
    have hh : c x.1 = c y.1 := by
      change c x.1 * f x.2 = c y.1 * f y.2 at h
      rw [hxy] at h
      exact mul_right_cancel h
    exact Subtype.ext (Subtype.ext hh)
  let FN : C × A →* Subgroup.normalizer (Q : Set G) :=
    F.codRestrict _ (fun x => Subgroup.mul_mem _
      (Subgroup.center_le_normalizer _ (hcz x.1)) (hn x.2))
  apply primeRank_ge_of_elementary_embedding (p := 3) (e := 3) ?_ ?_ FN
  · intro x y h
    exact hF (congrArg Subtype.val h)
  · intro x
    apply Prod.ext
    · change x.1 ^ 3 = 1
      simpa only [hC] using pow_card_eq_one' (x := x.1)
    · exact ha x.2
  · rw [Nat.card_prod, hC, hc]
    decide

/-- The supplied nontrivial two-subgroup is the explicit two-local witness. -/
theorem three_le_twoLocalPrimeRank_of_three_dvd_center
    {G A : Type*} [Group G] [Finite G] [CommGroup A] [Finite A]
    (hd : 3 ∣ Nat.card (Subgroup.center G))
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (f : A →* G)
    (hf : Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp f))
    (hn : ∀ a, f a ∈ Subgroup.normalizer (Q : Set G))
    (ha : ∀ a : A, a ^ 3 = 1) (hc : Nat.card A = 3 ^ 2) :
    3 ≤ twoLocalPrimeRank 3 G := by
  have hlocal : IsTwoLocal (Subgroup.normalizer (Q : Set G)) := ⟨Q, hQne, hQ, rfl⟩
  exact (three_le_primeRank_normalizer_of_three_dvd_center
    hd Q f hf hn ha hc).trans (hlocal.primeRank_le 3)

end Theory.Quasithin
