module
public import Theory.GroupTheory.TwoOrbitOddPrime.Outer
public import Theory.GroupAction.ComponentRankAction

/-!
# Coprimality of kernels on two conjugate component quotients

Two commuting centerless subgroups with orders divisible by an odd prime p
use both units of the ambient p-rank. Their common centralizer therefore has
order prime to p. For two distinct conjugate C-components, apply this to their
images in the literal ambient two-core quotient. A subgroup acting trivially
on their join has p-prime image and a two-group kernel, hence p-prime order.

No assumption on the outer automorphism group is needed: this controls the
section kernel, rather than the index of the component join. The Chapter 10
application uses it for the Hall kernel in the FF branch of 10.2.3(2).

Source: Aschbacher--Smith, the prime-rank argument in 1.2.2, printed p.504,
and the coprimality inference in 10.2.3(2), printed p.745.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.TwoOrbitOddPrime
variable {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

private theorem center_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center A = ⊥) : center B = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have h : e.symm x ∈ center A := ((centerCongr e).symm ⟨x,hx⟩).property
  have he : e.symm x = 1 := by simpa only [hz,mem_bot] using h
  exact e.symm.map_eq_one_iff.mp he

/-- Two centerless commuting factors exhaust the available prime rank. -/
theorem pair_centralizer_coprime (L M : Subgroup G)
    (hcomm : ⁅L,M⁆ = ⊥) (hL : center L = ⊥) (hM : center M = ⊥)
    (hdL : p ∣ Nat.card L) (hdM : p ∣ Nat.card M) (hr : primeRank p G ≤ 2) :
    Nat.Coprime p (Nat.card (centralizer ((L ⊔ M : Subgroup G) : Set G))) := by
  have hlow : 2 ≤ primeRank p (L ⊔ M : Subgroup G) := by
    rw [primeRank_sup_eq_add_of_disjoint_commuting L M
      (disjoint_of_commuting_of_center_eq_bot hcomm hL)
      (commutator_eq_bot_iff_le_centralizer.mp hcomm)]
    have hLpos : primeRank p L ≠ 0 := fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h hdL
    have hMpos : primeRank p M ≠ 0 := fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h hdM
    omega
  apply Theory.GroupAction.ComponentRankAction.centralizer_coprime (L ⊔ M) _ hlow hr
  rw [TwoOrbitThree.join_center_eq_bot L M hcomm hL hM]
  simp

/-- Centralizing the two distinct component images forces p-prime order,
with the kernel lifted through the actual ambient two-core. -/
theorem cComponent_pair_sectionKernel_coprime (hp : p ≠ 2)
    {L : Subgroup G} (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hz : center (L ⧸ pCore 2 L) = ⊥)
    (t : G) (ht : t ∉ normalizer (L : Set G))
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) (hr : primeRank p G ≤ 2)
    (C : Subgroup G) (hc : ⁅C,L ⊔ L.conjBy t⁆ ≤ pCore 2 G) :
    Nat.Coprime p (Nat.card C) := by
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let q := QuotientGroup.mk' (pCore 2 G)
  let A := L.map q
  let e := cComponentTwoCoreQuotientEquiv hL
  have hzA : center A = ⊥ := center_transport e hz
  have hdA : p ∣ Nat.card A := by rwa [←Nat.card_congr e.toEquiv]
  have hcop := pair_centralizer_coprime p A (A.conjBy (q t))
    (TwoOrbitThree.quotient_pair_commutes hL t ht) hzA
    (center_transport ((MulAut.conj (q t)).subgroupMap A) hzA) hdA
    (by
      change p ∣ Nat.card (A.map (MulAut.conj (q t)).toMonoidHom)
      rwa [card_map_of_injective (MulAut.conj (q t)).injective])
    ((primeRank_quotient_le_of_isTwoGroup p ((Fact.out : p.Prime).odd_of_ne_two hp)
      _ pCore_isPGroup).trans hr)
  have hC : C.map q ≤ centralizer ((A ⊔ A.conjBy (q t) : Subgroup _) : Set _) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←TwoOrbitThree.pair_map_quotient,←map_commutator,Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact hc
  let f := q.comp C.subtype
  have hf : f.range = C.map q := by rw [MonoidHom.range_comp,range_subtype]
  have him : Nat.Coprime p (Nat.card f.range) := by
    rw [hf]
    exact hcop.coprime_dvd_right (card_dvd_of_le hC)
  let j : f.ker →* pCore 2 G :=
    { toFun := fun x => ⟨x.val.val,(QuotientGroup.eq_one_iff _).mp x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x : pCore 2 G => x.val) hab))
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.of_injective j hj
  have hker : Nat.Coprime p (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp).coprime_two_right.pow_right n
  rw [card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact him.mul_right hker
end Theory.GroupTheory.TwoOrbitOddPrime
