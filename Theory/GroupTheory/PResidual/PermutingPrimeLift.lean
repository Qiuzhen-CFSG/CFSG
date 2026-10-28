module
public import Theory.GroupTheory.SolvableSylowSupplement
public import Theory.GroupTheory.Hall.OddSylowComplement
public import Theory.GroupTheory.PrimeResidualIntersection

/-!
# Prime actors that permute with a prescribed Sylow subgroup

Suppose the two-residual of a finite quotient has prime order p. A solvable
supplement to the solvable residual, containing the prescribed Sylow
two-subgroup, still maps onto that quotient. A Hall {2,p}-subgroup of the
supplement also maps onto it. Its odd complement is a p-group whose image
is exactly the quotient's two-residual. Both orders of the product with the
original Sylow subgroup equal the Hall subgroup.

This construction does not require the original group or the quotient
kernel to be solvable. It supplies the prime actor in Aschbacher--Smith
15.1.21(ii), printed p.1098, without changing the Sylow subgroup.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
open scoped Pointwise

private theorem odd_twoPerfect {A : Type*} [Group A] [Finite A]
    (ho : Odd (Nat.card A)) : IsPPerfect 2 A := by
  intro N hn htwo
  let := hn
  apply index_eq_one.mp
  change Nat.card (A ⧸ N) = 1
  apply htwo.card_eq_or_dvd.resolve_right
  intro hd
  exact (Nat.not_even_iff_odd.mpr ho)
    (even_iff_two_dvd.mpr (hd.trans N.card_quotient_dvd_card))

private theorem prime_residual_solvable {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime] (hc : Nat.card (pResidual 2 Q) = p) :
    Group.IsSolvable Q := by
  let : IsCyclic (pResidual 2 Q) := isCyclic_of_prime_card hc
  let : Group.IsNilpotent (Q ⧸ pResidual 2 Q) := (isPGroup_quotient_pResidual 2).isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pResidual 2 Q)).mpr ⟨inferInstance, inferInstance⟩

private theorem prime_residual_prime_divisors {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hc : Nat.card (pResidual 2 Q) = p) (hp : p.Prime)
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card Q) : r = 2 ∨ r = p := by
  obtain ⟨n, hn⟩ := (isPGroup_quotient_pResidual (G := Q) 2).exists_card_eq
  have he := (pResidual 2 Q).card_mul_index
  rw [hc, index_eq_card, hn] at he
  rw [← he] at hd
  rcases hr.dvd_mul.mp hd with hd | hd
  · exact Or.inr ((Nat.dvd_prime hp).mp hd |>.resolve_left hr.ne_one)
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow hd) |>.resolve_left hr.ne_one)

/-- A prime residual in a quotient has a prime-group lift permuting with the given Sylow. -/
theorem exists_permuting_prime_residual_lift
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
    (f : G →* Q) (hf : Function.Surjective f) (S : Sylow 2 G)
    {p : ℕ} [Fact p.Prime] (hc : Nat.card (pResidual 2 Q) = p) :
    ∃ Y : Subgroup G, IsPGroup p Y ∧ IsPPerfect 2 Y ∧
      (S : Set G) * (Y : Set G) = (Y : Set G) * (S : Set G) ∧
      Y.map f = pResidual 2 Q ∧ Y ≤ pResidual 2 G := by
  classical
  let : Group.IsSolvable Q := prime_residual_solvable hc
  obtain ⟨N, hNsol, hSN, hN⟩ := exists_solvable_sylow_supplement S
  let := hNsol
  have hRf : (solvableResidual G).map f = ⊥ := by
    apply bot_unique
    exact (map_solvableResidual_le f).trans_eq solvableResidual_eq_bot
  have hNf : N.map f = ⊤ := by
    have he := congrArg (map f) hN
    simpa only [Subgroup.map_sup, hRf, sup_bot_eq, map_top_of_surjective f hf] using he
  let fN := f.comp N.subtype
  have hfN : Function.Surjective fN := by
    intro q
    obtain ⟨g, hg, he⟩ := hNf.symm ▸ (mem_top q : q ∈ (⊤ : Subgroup Q))
    exact ⟨⟨g, hg⟩, he⟩
  let SN := S.subtype hSN
  let π : Set Nat.Primes := {r | r.val = 2 ∨ r.val = p}
  let : MulDistribMulAction Unit N := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  have hSNpi : IsPiSubgroup π (SN : Subgroup N) := by
    intro r hr
    obtain ⟨n, hn⟩ := SN.isPGroup'.exists_card_eq
    rw [hn] at hr
    exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (r.property.dvd_of_dvd_pow hr) |>.resolve_left r.property.ne_one)
  obtain ⟨H, hHall, _, hSH⟩ := exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (A := Unit) hNsol (by simp) π (SN : Subgroup N) hSNpi ⟨fun _ _ => Iff.rfl⟩
  have hHf : H.map fN = ⊤ := by
    apply index_eq_one.mp
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro r hr hd
    have hdiv := hd.trans (H.map fN).index_dvd_card
    have hpi : (⟨r,hr⟩ : Nat.Primes) ∈ π := prime_residual_prime_divisors hc Fact.out hr hdiv
    exact hHall.p_in_pi_of_p_dvd_index ⟨r,hr⟩ (hd.trans (H.index_map_dvd hfN)) hpi
  obtain ⟨A, hAodd, hcomp⟩ := exists_odd_complement_sylow_two
    (inferInstance : Group.IsSolvable H) (SN.subtype hSH)
  have hAp : IsPGroup p A := by
    apply IsPGroup.of_card
    apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    intro r hr hd
    have hpi := hHall.p_in_pi_of_p_dvd_card ⟨r,hr⟩ (hd.trans A.card_subgroup_dvd_card)
    rcases hpi with htwo | hp
    · exact False.elim ((Nat.not_even_iff_odd.mpr hAodd) (even_iff_two_dvd.mpr (htwo ▸ hd)))
    · exact hp
  let j : H →* G := N.subtype.comp H.subtype
  let Y := A.map j
  have hSY (hcomp : ((SN.subtype hSH : Sylow 2 H) : Subgroup H).IsComplement' A) :
      (S : Set G) * (Y : Set G) = (H.map N.subtype : Set G) := by
    ext x
    constructor
    · rintro ⟨s, hs, a, ⟨a', ha', rfl⟩, rfl⟩
      exact ⟨⟨s, hSN hs⟩ * (a' : N), H.mul_mem (hSH hs) a'.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨⟨s, a⟩, he⟩ := hcomp.2 ⟨x,hx⟩
      refine ⟨s.val.val.val, s.property, j a.val, ⟨a, a.property, rfl⟩, ?_⟩
      exact congrArg (fun z : H => (z.val : G)) he
  have hperm : (S : Set G) * (Y : Set G) = (Y : Set G) * (S : Set G) := by
    rw [hSY hcomp]
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨⟨a, s⟩, he⟩ := hcomp.symm.2 (⟨x,hx⟩ : H)
      exact ⟨j a.val, ⟨a, a.property, rfl⟩, s.val.val.val, s.property,
        congrArg (fun z : H => (z.val : G)) he⟩
    · rintro ⟨a, ⟨a', ha', rfl⟩, s, hs, rfl⟩
      exact ⟨(a' : N) * ⟨s, hSN hs⟩, H.mul_mem a'.property (hSH hs), rfl⟩
  have hYperfect : IsPPerfect 2 Y := (odd_twoPerfect hAodd).of_surjective
    (j.subgroupMap A) (j.subgroupMap_surjective A)
  have hYR : Y ≤ pResidual 2 G := le_pResidual_of_isPPerfect Y hYperfect
  have hYfR : Y.map f ≤ pResidual 2 Q :=
    (map_mono hYR).trans (map_pResidual_le 2 f)
  have hgen : (S : Subgroup G) ⊔ Y = H.map N.subtype := by
    apply le_antisymm
    · refine sup_le ?_ (map_mono (show A ≤ ⊤ from le_top) |>.trans ?_)
      · intro x hx
        exact ⟨⟨x,hSN hx⟩,hSH hx,rfl⟩
      · intro x hx
        obtain ⟨a, _, rfl⟩ := hx
        exact ⟨a.val,a.property,rfl⟩
    · intro x hx
      have hx' : x ∈ (S : Set G) * (Y : Set G) := (hSY hcomp).symm ▸ hx
      obtain ⟨s, hs, y, hy, rfl⟩ := hx'
      exact mul_mem_sup hs hy
  have hYf : Y.map f = pResidual 2 Q := by
    let R := pResidual 2 Q
    let : Fact (Nat.card R).Prime := ⟨hc ▸ Fact.out⟩
    rcases ((Y.map f).subgroupOf R).eq_bot_or_eq_top_of_prime_card with hb | ht
    · have hbot : Y.map f = ⊥ := by
        have he := congrArg (map R.subtype) hb
        simpa only [map_subgroupOf_eq_of_le (show Y.map f ≤ R from hYfR), Subgroup.map_bot] using he
      have hSf : (S : Subgroup G).map f = ⊤ := by
        have he := congrArg (map f) hgen
        rw [Subgroup.map_sup, hbot, sup_bot_eq, map_map] at he
        exact he.trans hHf
      have hQtwo : IsPGroup 2 Q := (S.isPGroup'.map f).of_equiv
        (MulEquiv.subgroupCongr hSf |>.trans Subgroup.topEquiv)
      have hRbot : R = ⊥ := by
        apply bot_unique
        exact pResidual_le_ker_of_isPGroup 2 (MonoidHom.id Q) hQtwo
      have : p = 1 := by
        change Nat.card R = p at hc
        simpa only [hRbot, card_bot] using hc.symm
      exact (Fact.out : p.Prime).ne_one this |>.elim
    · apply le_antisymm hYfR
      intro q hq
      exact show (⟨q,hq⟩ : R) ∈ (Y.map f).subgroupOf R from ht ▸ mem_top _
  exact ⟨Y, hAp.map j, hYperfect, hperm, hYf, hYR⟩

end Subgroup
