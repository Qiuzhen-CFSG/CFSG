module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalCoordinates
public import Theory.GroupTheory.PResidual.PrimeToSubnormal

/-!
# Applying the prime-to-p residual clauses to the source D₀

If every prime greater than three dividing the odd Hall subgroup is removed
from the index of L in M, its image modulo L is a 3-group. Its 3-residual
therefore lies in L. The generators of Ω₁(O₃(D)) are handled separately by
the order-three clause. For Sp₄ that clause follows from O^{3′}(M)=L;
for SL₃ the torus prime support forces even field degree.

The application retains both full source models and the exact 11.0.4
residual convention. Prime support is still a Hall-geometry obligation;
11.0.4 itself is supplied by the earlier local-geometry owner.
Source: Aschbacher--Smith, 11.0.4 and 11.3.7(2), printed pp.760,773.
-/

open Subgroup Theory.GroupTheory
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G]

/-- The exact prime-to-p residual clauses force the odd quotient to be a 3-group. -/
theorem odd_residual_le_of_primeToResidual
    (A M N : Subgroup G) (hAM : A ≤ M)
    [(N.subgroupOf M).Normal] (ho : Odd (Nat.card A))
    (hr : ∀ p : ℕ, p.Prime → 3 < p → p ∣ Nat.card A →
      primeToResidual p M ≤ N.subgroupOf M) :
    (pResidual 3 A).map A.subtype ≤ N := by
  let f : A →* M ⧸ N.subgroupOf M :=
    (QuotientGroup.mk' (N.subgroupOf M)).comp (inclusion hAM)
  have hf : IsPGroup 3 f.range := by
    apply (isPGroup_iff_primeFactors_card_subset (by decide : 3 ≠ 0)).mpr
    intro p hp
    obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hp
    have hA : p ∣ Nat.card A := hd.trans (card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective)
    have hp2 : p ≠ 2 := by
      intro he
      subst p
      exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hA)
    have hp3 : p = 3 := by
      by_contra hne
      let : Fact p.Prime := ⟨hp⟩
      have hl : 3 < p := by have := hp.two_le; omega
      have hi : Nat.Coprime p (N.subgroupOf M).index :=
        (primeToResidual_index_coprime p).of_dvd_right (index_dvd_of_le (hr p hp hl hA))
      have hdiv : p ∣ (N.subgroupOf M).index := by
        change p ∣ Nat.card (M ⧸ N.subgroupOf M)
        exact hd.trans f.range.card_subgroup_dvd_card
      exact (hp.coprime_iff_not_dvd.mp hi) hdiv
    subst p
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, dvd_refl _, by decide⟩
  have hk : pResidual 3 A ≤ f.ker :=
    sInf_le ⟨inferInstance, hf.of_equiv (QuotientGroup.quotientKerEquivRange f).symm⟩
  rintro x ⟨a, ha, rfl⟩
  have hh := hk ha
  change QuotientGroup.mk' (N.subgroupOf M) (inclusion hAM a) = 1 at hh
  exact (QuotientGroup.eq_one_iff (inclusion hAM a)).mp hh

/-- The order-three clause is used only on the generators of Ω₁(O₃(A)). -/
theorem oddCartanPart_le_of_primeToResidual
    (A M N : Subgroup G) (hAM : A ≤ M)
    [(N.subgroupOf M).Normal] (ho : Odd (Nat.card A))
    (hr : ∀ p : ℕ, p.Prime → 3 < p → p ∣ Nat.card A →
      primeToResidual p M ≤ N.subgroupOf M)
    (hthree : ∀ a ∈ A, orderOf a = 3 → a ∈ N) :
    oddCartanPart A ≤ N := by
  rw [oddCartanPart, Subgroup.map_sup]
  apply sup_le (odd_residual_le_of_primeToResidual A M N hAM ho hr)
  rw [map_map, map_le_iff_le_comap]
  apply (closure_le _).2
  intro a ha
  have ha3 : a ^ 3 = 1 := by simpa using ha
  have hz : (a.val.val : G) ^ 3 = 1 := congrArg (fun z : pCore 3 A => (z.val.val : G)) ha3
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hz) with he | he
  · have hone : (a.val.val : G) = 1 := orderOf_eq_one_iff.mp he
    change (a.val.val : G) ∈ N
    rw [hone]
    exact N.one_mem
  · exact hthree _ a.val.property he

/-- The source 11.0.4 clauses, applied to the actual Hall subgroup. The order
support is the separate rank-one Hall calculation, not an extra residual convention. -/
theorem source_oddCartanPart_le
    {T : Sylow 2 G} {L V H : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card A → p ∣ 2 ^ S.field.degree - 1)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    oddCartanPart A ≤ L := by
  let M := normalizer (L : Set G)
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have ho : Odd (Nat.card A) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv]
    exact OddHall.odd_hall_odd hHall
  have hpow : 1 ≤ 2 ^ S.field.degree := Nat.one_le_pow _ _ (by decide)
  have hdiv (p : ℕ) (hp : p ∣ 2 ^ S.field.degree - 1) :
      p ∣ (2 ^ S.field.degree) ^ 2 - 1 := by
    exact hp.trans (Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2)
  apply oddCartanPart_le_of_primeToResidual A M L (hA.trans inf_le_right)
    ho
  · intro p hp hlarge hd
    exact (hres p hp (halt.elim
      (fun hs => Or.inl ⟨hs, hsupport p hp hd, hlarge⟩)
      (fun hs => Or.inr ⟨hs, hdiv p (hsupport p hp hd)⟩))).le
  · intro x hx hx3
    have hd : 3 ∣ 2 ^ S.field.degree - 1 :=
      hsupport 3 Nat.prime_three (hx3 ▸ A.orderOf_dvd_natCard hx)
    rcases halt with hs | hs
    · have he : Even S.field.degree := by
        by_contra hn
        have hnmod : 2 ^ S.field.degree % 3 = 2 := by
          obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hn
          rw [hk]
          simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
        have hm := Nat.mod_eq_zero_of_dvd hd
        omega
      exact hcubic hs he x (hA hx).2 hx3
    · have hr := hres 3 Nat.prime_three (Or.inr ⟨hs, hdiv 3 hd⟩)
      have hxpow : (⟨x, (hA hx).2⟩ : M) ^ (3 ^ 1) = 1 := by
        apply Subtype.ext
        simpa only [Subgroup.coe_pow, Subgroup.coe_one, pow_one, hx3] using pow_orderOf_eq_one x
      have hm := mem_primeToResidual_of_pow hxpow
      rw [hr] at hm
      exact hm
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
