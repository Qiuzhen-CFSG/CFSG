module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeTerminal
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedHall.Orbit
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankCoprimeIndex
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSmallGeneration

/-!
# Prime Hall rank and exchanged linear Cartan normalization

The odd Hall group B normalizes the order-three or order-five subgroup D
of the cyclic left Cartan. Since Aut(D) is a two-group, B centralizes D.
The zero core of DH and the nonzero core of H make D disjoint from B.
Thus their commuting product adds one to the p-rank, and quasithinness
of N_G(L) bounds the p-rank of B, and of N_G(L) intersect H, by one.

In an exchanged source row the component images modulo O₂(H) are actual
commuting components. If p divides the order of their Borel overlap,
two distinct conjugate overlaps contradict that rank bound. The marked
linear torus therefore has order prime to p. When the original left
degree is two or four and divides the marked right degree, the small
Cartan generators prove the original normalization conclusion.

The degrees remain distinct and the source marking is in H/core_H(M).
This proves the indicated exchanged linear branch; it does not select a
right factor or settle the other source rows of the local-to-global task.
Source: Aschbacher--Smith 5.1.10(1) and 5.2.2, printed pp.634,646--649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The full odd right Hall group fixes either possible prime actor pointwise. -/
theorem CartanPair.centralizes_prime_actor {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H p D) : B ≤ centralizer (D : Set G) := by
  have hp : p.Prime := by rcases hd.prime with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic D := isCyclic_of_prime_card hd.card
  let f := D.normalizerMonoidHom.comp (inclusion (c.normalizes_prime_actor h hd))
  have ho : Odd (Nat.card B) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
    exact OddHall.odd_hall_odd c.right_hall
  have hc : Nat.Coprime (Nat.card B) (Nat.card (MulAut D)) := by
    rw [IsCyclic.card_mulAut, hd.card]
    rcases hd.prime with rfl | rfl
    · rw [show Nat.totient 3 = 2 by decide]
      exact Nat.coprime_two_right.mpr ho
    · rw [show Nat.totient 5 = 2 ^ 2 by decide]
      exact (Nat.coprime_two_right.mpr ho).pow_right 2
  have hc1 : Nat.card f.range = 1 := Nat.eq_one_of_dvd_coprimes hc
    (card_range_dvd f) f.range.card_subgroup_dvd_card
  have hf (b : B) : f b = 1 :=
    mem_bot.mp ((f.range.eq_bot_of_card_eq hc1) ▸ (show f b ∈ f.range from ⟨b,rfl⟩))
  intro b hb d hd
  have he := congrArg (fun z : MulAut D => (z (⟨d,hd⟩ : D) : G)) (hf ⟨b,hb⟩)
  change b * d * b⁻¹ = d at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

omit [Finite G] in
/-- A zero-core actor meets the right Hall group trivially, since B lies in H. -/
theorem CartanPrimeActor.disjoint_right_cartan
    {T : Sylow 2 G} {L H A B D : Subgroup G} {p : ℕ}
    (hd : CartanPrimeActor A H p D) (c : CartanPair T L H A B)
    (hH : H.pCoreIn 2 ≠ ⊥) : Disjoint D B := by
  have hp : (Nat.card D).Prime := by
    rw [hd.card]
    rcases hd.prime with rfl | rfl <;> decide
  let : Fact (Nat.card D).Prime := ⟨hp⟩
  rcases (B.subgroupOf D).eq_bot_or_eq_top_of_prime_card with hb | ht
  · apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hx' : (⟨x,hx.1⟩ : D) ∈ B.subgroupOf D := hx.2
    rw [hb] at hx'
    exact congrArg Subtype.val (mem_bot.mp hx')
  · have hDB := subgroupOf_eq_top.mp ht
    have hDH := hDB.trans (c.right_le.trans inf_le_right)
    exact (hH (by simpa only [sup_eq_right.mpr hDH] using hd.zero_core)).elim

/-- An escaping prime actor leaves at most one p-direction in the actual right Hall group. -/
theorem CartanPair.right_primeRank_le_one {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H p D) (hH : H.pCoreIn 2 ≠ ⊥) :
    primeRank p B ≤ 1 := by
  have hp : p.Prime := by rcases hd.prime with rfl | rfl <;> decide
  have ho : Odd p := by rcases hd.prime with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic D := isCyclic_of_prime_card hd.card
  let : CommGroup D := IsMulCommutative.instCommGroup
  have hrD : 1 ≤ primeRank p D := primeRank_ge_of_elementary_embedding
    (fun x : D => by simpa only [hd.card] using pow_card_eq_one' (x := x))
    (by simpa using hd.card) (MonoidHom.id D) Function.injective_id
  have he := D.primeRank_sup_eq_add_of_disjoint_commuting B
    (hd.disjoint_right_cartan c hH)
    (le_centralizer_iff.mp (c.centralizes_prime_actor h hd)) p
  have hJM : D ⊔ B ≤ normalizer (L : Set G) := sup_le
    ((hd.le_cartan.trans c.left_le).trans (inf_le_left.trans L.le_normalizer))
    (c.right_le.trans inf_le_left)
  have hl := primeRank_mono p hJM
  have hu := isQuasithin_iff_twoLocal.mp h.qtke.quasithin
    (normalizer (L : Set G)) h.maximal.1 p hp ho
  omega

/-- The Hall index is prime to p, so the same bound holds on the literal overlap. -/
theorem CartanPair.overlap_primeRank_le_one {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H p D) (hH : H.pCoreIn 2 ≠ ⊥) :
    primeRank p (normalizer (L : Set G) ⊓ H : Subgroup G) ≤ 1 := by
  have hp : p.Prime := by rcases hd.prime with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hp⟩
  have hne : p ≠ 2 := by rcases hd.prime with rfl | rfl <;> decide
  have hi : ¬ p ∣ (B.subgroupOf (normalizer (L : Set G) ⊓ H)).index := by
    intro hi
    exact c.right_hall.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hi hne
  rw [← (B.subgroupOf (normalizer (L : Set G) ⊓ H)).primeRank_eq_of_not_dvd_index hi,
    primeRank_equiv p (subgroupOfEquivOfLe c.right_le)]
  exact c.right_primeRank_le_one h hd hH
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
private theorem IsComponent.overlap_rank_one_normalizes
    {C M : Subgroup G} (hC : IsComponent G C) (hz : center C = ⊥)
    (p : ℕ) [Fact p.Prime] (hr : primeRank p M ≤ 1)
    (ho : 1 ≤ primeRank p (M ⊓ C : Subgroup G)) :
    M ≤ normalizer (C : Set G) := by
  intro m hm
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  let B := M ⊓ C
  let B' := B.map (MulAut.conj m).toMonoidHom
  have hc : C ≤ centralizer (C.map (MulAut.conj m).toMonoidHom : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (hC.commutator_eq_bot_of_ne (hC.map_conj m) (Ne.symm hne))
  have hdis : Disjoint B B' := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hx,hx'⟩
    have hxC : x ∈ C := hx.2
    have hxC' : x ∈ C.map (MulAut.conj m).toMonoidHom := map_mono inf_le_right hx'
    have hxc : (⟨x,hxC⟩ : C) ∈ center C := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext ((le_centralizer_iff.mp hc) hxC' y y.property)
    have hx1 : (⟨x,hxC⟩ : C) = 1 := by simpa only [hz, mem_bot] using hxc
    exact congrArg (fun c : C => (c : G)) hx1
  have hcomm : B ≤ centralizer (B' : Set G) :=
    inf_le_right.trans (hc.trans (centralizer_le (map_mono inf_le_right)))
  have hB'M : B' ≤ M := by
    exact (map_mono (show B ≤ M from inf_le_left)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hm))
  have hbound := primeRank_mono p (sup_le (show B ≤ M from inf_le_left) hB'M)
  rw [B.primeRank_sup_eq_add_of_disjoint_commuting B' hdis hcomm p] at hbound
  have hsame : primeRank p B = primeRank p B' :=
    primeRank_equiv p ((MulAut.conj m).subgroupMap B)
  rw [← hsame] at hbound
  change primeRank p (M ⊓ C : Subgroup G) + primeRank p (M ⊓ C : Subgroup G) ≤
    primeRank p M at hbound
  omega
end Theory.GroupTheory

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

private theorem rank_pos_of_prime_dvd (p : ℕ) [Fact p.Prime]
    (hd : p ∣ Nat.card G) : 1 ≤ primeRank p G := by
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := G) p hd
  let E := zpowers x
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hc : Nat.card E = p := (Nat.card_zpowers x).trans hx
  exact primeRank_ge_of_elementary_embedding
    (fun y : E => by simpa only [hc] using pow_card_eq_one' (x := y))
    (by simpa using hc) E.subtype E.subtype_injective

private theorem exchanged_overlap_prime_not_dvd
    {M C T : Subgroup G} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses M C T) (hz : center (sourceImage M C) = ⊥)
    (hTM : T ≤ M) (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (hr : primeRank p M ≤ 1) :
    ¬ p ∣ Nat.card (sourceImage M (M ⊓ C)) := by
  intro hd
  let q := QuotientGroup.mk' (sourceKernel M)
  have hker : IsPGroup 2 (q.subgroupMap M).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk', hc.kernel_eq]
    exact pCore_isPGroup.comap_subtype
  have hrq : primeRank p (sourceImage M M) ≤ 1 := by
    apply (primeRank_le_of_surjective_of_coprime p (q.subgroupMap M)
      (q.subgroupMap_surjective M) ?_).trans hr
    obtain ⟨k,hk⟩ := hker.exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hp).pow_right k
  have hnorm : sourceImage M M ≤ normalizer (sourceImage M C : Set _) := by
    apply (ExchangedHall.source_component hc hC hqs).overlap_rank_one_normalizes hz p hrq
    rw [← ExchangedHall.source_overlap_eq]
    exact rank_pos_of_prime_dvd p hd
  obtain ⟨t,ht,hne,_⟩ := hc.exchanged_product
  have htq : q t⁻¹ ∈ normalizer (sourceImage M C : Set _) :=
    hnorm (mem_map_of_mem q (hTM (T.inv_mem ht)))
  have htN : t⁻¹ ∈ normalizer (C : Set G) := by
    let : Group.IsNilpotent (sourceKernel M) := hc.kernel_eq.symm ▸ pCore_isNilpotent
    rw [← normalizer_cComponent_quotient hC (sourceKernel M)]
    exact htq
  exact hne (mem_normalizer_iff_map_conj_eq.mp htN).symm

/-- The actual exchanged source overlap has order prime to the escaping actor. -/
theorem CartanPair.exchanged_source_overlap_prime_not_dvd {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H p D)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hz : center (sourceImage ((normalizer (L : Set G)).subgroupOf H) C) = ⊥) :
    ¬ p ∣ Nat.card (sourceImage ((normalizer (L : Set G)).subgroupOf H)
      (((normalizer (L : Set G)).subgroupOf H) ⊓ C)) := by
  have hp : p.Prime := by rcases hd.prime with rfl | rfl <;> decide
  have ho : Odd p := by rcases hd.prime with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hp⟩
  apply exchanged_overlap_prime_not_dvd hC hqs hc hz
    (comap_mono h.sylow_normalizes) p ho
  have he : ((normalizer (L : Set G) ⊓ H).subgroupOf H) =
      (normalizer (L : Set G)).subgroupOf H := inf_subgroupOf_right _ _
  rw [← he, primeRank_equiv p (subgroupOfEquivOfLe inf_le_right)]
  exact c.overlap_primeRank_le_one h hd hH.1.1.1

/-- The marked right linear torus cannot contain the prime of a zero-core left actor. -/
theorem CartanPair.exchanged_linear_torus_prime_not_dvd {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H p D)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ f)
    (hm : ModelBorelPair ((normalizer (L : Set G)).subgroupOf H) C
      (BenderSuzuki.Converse.PBorel F)) : ¬ p ∣ 2 ^ f - 1 := by
  obtain ⟨e,he⟩ := hm
  have hz : center (sourceImage ((normalizer (L : Set G)).subgroupOf H) C) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := ((centerCongr e) ⟨x,hx⟩).property
    change e x ∈ center (BenderSuzuki.Converse.PSL2 F) at hh
    rw [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot] at hh
    exact e.map_eq_one_iff.mp (mem_bot.mp hh)
  have hnot := c.exchanged_source_overlap_prime_not_dvd h hd hH hC hqs hc hz
  have hcB : Nat.card (BenderSuzuki.Converse.PBorel F) =
      Nat.card (sourceImage ((normalizer (L : Set G)).subgroupOf H)
        (((normalizer (L : Set G)).subgroupOf H) ⊓ C)) := by
    rw [← he, card_map_of_injective e.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe (show
      sourceImage ((normalizer (L : Set G)).subgroupOf H) (((normalizer (L : Set G)).subgroupOf H) ⊓ C) ≤
        sourceImage ((normalizer (L : Set G)).subgroupOf H) C from map_mono inf_le_right)).toEquiv
  intro hdiv
  apply hnot
  rw [← hcB]
  apply hdiv.trans
  have hh := card_dvd_of_le (BenderSuzuki.Converse.PTorus_le_PBorel (F := F))
  rwa [BenderSuzuki.Converse.PTorus_card, Nat.card_units, hF] at hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- On an exchanged linear row whose degree is divisible by the original small
left degree, local Cartan control already implies the requested normalization. -/
theorem Input.cartan_normalizes_of_exchanged_linear_small_degree {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n f : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hn : n = 2 ∨ n = 4) (hnf : n ∣ f)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ f)
    (hm : ModelBorelPair ((normalizer (L : Set G)).subgroupOf H) C
      (BenderSuzuki.Converse.PBorel F)) :
    A ≤ normalizer (residual H : Set G) := by
  by_contra hnot
  have hcard := (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  have hs := cartanSmallGeneration_of_degree_two_or_four hH hcard hn
  obtain ⟨p,D,hd⟩ := hs.exists_prime_actor hcontrol hnot
  apply c.exchanged_linear_torus_prime_not_dvd h hd hH hC hqs hc hF hm
  have hdiv : p ∣ 2 ^ n - 1 := by
    rw [← hcard, ← hd.card]
    exact card_dvd_of_le hd.le_cartan
  exact hdiv.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hnf)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
