module
public import Theory.GroupTheory.Commutator.CentralAbelianSylow
public import Theory.GroupAction.IrreducibleSmallLinear
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# Inner actors in an ambient group of odd prime rank two

A noncentral element of order p in N gives a p-line disjoint from C(N).
The commuting-product rank formula bounds the centralizer's p-rank by one,
so its odd Sylow subgroups and the p-subgroups in its images are cyclic.
An irreducible noncyclic Frattini actor inside N C(N) consequently has
cyclic image modulo N. Irreducibility kills that image and gives P ≤ N.

When the center of N has order prime to p, nontrivial inner p-action
supplies the required noncentral prime-order element by Cauchy's theorem.
The witness version also applies when p divides the center. Finally, for
an exponent-p actor and perfect N, the witness is unnecessary. An escaping
order-p element bounds the center rank by one; if all order-p elements of
N were central, odd Sylow cyclicity and central transfer would contradict
p dividing |N|. No order-p lift of an inner automorphism is assumed.

Source application: Aschbacher–Smith, Proposition 1.3.4, printed p.510.
-/

public section
open Theory.GroupTheory
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem primeRank_centralizer_le_one_of_noncentral_prime (N : Subgroup G) (x : N) (hx : orderOf x = p)
    (hn : x ∉ center N) (hr : primeRank p G ≤ 2) :
    primeRank p (centralizer (N : Set G)) ≤ 1 := by
  let C := centralizer (N : Set G)
  let U := zpowers (x : G)
  have hxG : orderOf (x : G) = p := (orderOf_injective N.subtype N.subtype_injective x).trans hx
  have hxC : (x : G) ∉ C := by
    intro hc
    apply hn
    exact mem_center_iff.mpr fun n => Subtype.ext (hc n n.property)
  have hd : Disjoint U C := (C.disjoint_zpowers_of_prime_order_not_mem x hxG hxC).symm
  have hUN : U ≤ N := zpowers_le.mpr x.property
  have hUC : U ≤ centralizer (C : Set G) := hUN.trans (le_centralizer_iff.mp le_rfl)
  have hUc : Nat.card U = p := (Nat.card_zpowers _).trans hxG
  have hUp (u : U) : u ^ p = 1 := hUc ▸ pow_card_eq_one' (x := u)
  let : CommGroup U := IsMulCommutative.instCommGroup
  have hUr : 1 ≤ primeRank p U :=
    primeRank_ge_of_elementary_embedding hUp (by simpa using hUc)
      (MonoidHom.id U) Function.injective_id
  have he := U.primeRank_sup_eq_add_of_disjoint_commuting C hd hUC p
  have hle := primeRank_le_of_injective p (U ⊔ C).subtype (U ⊔ C).subtype_injective
  change primeRank p C ≤ 1
  omega

omit [Finite G] in
theorem prime_dvd_card_of_nontrivial_inner_pGroup {P : Subgroup G} (hP : IsPGroup p P)
    (N : Subgroup G) [N.Normal] (hinner : P ≤ N ⊔ centralizer (N : Set G))
    (hnc : ⁅N,P⁆ ≠ ⊥) : p ∣ Nat.card N := by
  by_contra hn
  have hcop := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn
  have hPC : P ≤ centralizer (N : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    intro x hx
    have hin : (MulAut.conjNormal x : MulAut N) ∈ MulAut.innerSubgroup N := by
      change x ∈ (MulAut.innerSubgroup N).comap (MulAut.conjNormal : G →* MulAut N)
      rw [MulAut.conjNormal_comap_innerSubgroup]
      exact hinner hx
    let a : MulAut.innerSubgroup N := ⟨MulAut.conjNormal x, hin⟩
    have hd : orderOf a ∣ Nat.card N :=
      (_root_.orderOf_dvd_natCard a).trans (card_range_dvd (MulAut.conj : N →* MulAut N))
    have hda : orderOf a ∣ orderOf (⟨x,hx⟩ : P) := by
      rw [← orderOf_injective (MulAut.innerSubgroup N).subtype
        (MulAut.innerSubgroup N).subtype_injective a]
      exact orderOf_map_dvd ((MulAut.conjNormal : G →* MulAut N).comp P.subtype) ⟨x,hx⟩
    have ha : a = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hP.orderOf_coprime hcop ⟨x,hx⟩) hda hd)
    exact congrArg Subtype.val ha
  exact hnc (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hPC))

theorem IsNormalizerFrattiniIrreducible.le_normal_of_inner_of_noncentral_prime
    {P : Subgroup G} (hirr : IsNormalizerFrattiniIrreducible P)
    (hP : IsPGroup p P) (hp : Odd p) (hnc : ¬ IsCyclic P)
    (hr : primeRank p G ≤ 2) (N : Subgroup G) [N.Normal]
    (hinner : P ≤ N ⊔ centralizer (N : Set G))
    (x : N) (hx : orderOf x = p) (hxN : x ∉ center N) : P ≤ N := by
  let C := centralizer (N : Set G)
  let q := QuotientGroup.mk' N
  have hCr : primeRank p C ≤ 1 := primeRank_centralizer_le_one_of_noncentral_prime N x hx hxN hr
  let S : Sylow p C := Classical.choice inferInstance
  have hCqr : primeRank p (C.map q) ≤ 1 := S.primeRank_le_one_of_surjective
    (S.isCyclic_of_odd_of_primeRank_le_one hp hCr) (q.subgroupMap C) (q.subgroupMap_surjective C)
  have hPC : P.map q ≤ C.map q := by
    have h := map_mono (f := q) hinner
    rwa [map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h
  have hPr : primeRank p (P.map q) ≤ 1 :=
    (primeRank_le_of_injective p (inclusion hPC) (inclusion_injective hPC)).trans hCqr
  have hcyc : IsCyclic (P.map q) := (hP.map q).isCyclic_of_odd_of_elementary_card_le hp
    (fun E he => by
      let := he
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hPr E)
  have hf : q.comp P.subtype = 1 := hirr.comp_eq_one_of_cyclic_range hnc q (by
    rwa [MonoidHom.range_comp, range_subtype])
  intro y hy
  exact (QuotientGroup.eq_one_iff y).mp (DFunLike.congr_fun hf ⟨y,hy⟩)

theorem IsNormalizerFrattiniIrreducible.le_normal_of_inner_of_coprime_center
    {P : Subgroup G} (hirr : IsNormalizerFrattiniIrreducible P)
    (hP : IsPGroup p P) (hp : Odd p) (hnc : ¬ IsCyclic P)
    (hr : primeRank p G ≤ 2) (N : Subgroup G) [N.Normal]
    (hinner : P ≤ N ⊔ centralizer (N : Set G)) (hmove : ⁅N,P⁆ ≠ ⊥)
    (hZ : ¬ p ∣ Nat.card (center N)) : P ≤ N := by
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p
    (prime_dvd_card_of_nontrivial_inner_pGroup hP N hinner hmove)
  have hxN : x ∉ center N := by
    intro hm
    exact hZ (hx ▸ (center N).orderOf_dvd_natCard hm)
  exact hirr.le_normal_of_inner_of_noncentral_prime hP hp hnc hr N hinner x hx hxN


/-- A noncyclic exponent-p actor with irreducible normalizer action, acting
nontrivially by inner automorphisms on a normal perfect subgroup, is contained
in that subgroup in an ambient group of odd p-rank at most two. -/
private theorem center_rank_of_escape (P N : Subgroup G)
    (hinner : P ≤ N ⊔ centralizer (N : Set G))
    (a : P) (ha : orderOf a = p) (haN : (a : G) ∉ N)
    (hr : primeRank p G ≤ 2) : primeRank p (center N) ≤ 1 := by
  let Z := (center N).map N.subtype
  have hNZ : N ≤ centralizer (Z : Set G) := by
    intro n hn z hz
    obtain ⟨z,hz,rfl⟩ := hz
    exact congrArg N.subtype (mem_center_iff.mp hz ⟨n,hn⟩).symm
  have hPZ : P ≤ centralizer (Z : Set G) := hinner.trans
    (sup_le hNZ (centralizer_le (map_subtype_le (center N))))
  obtain ⟨E,hE,hEc⟩ := exists_elementaryAbelian_card_primeRank (G := center N) (p := p)
  let f := N.subtype.comp (center N).subtype
  have hf : Function.Injective f := N.subtype_injective.comp (center N).subtype_injective
  let D := E.map f
  let := hE
  let : IsElementaryAbelian p D := IsElementaryAbelian.map f
  have hDZ : D ≤ Z := by
    intro d hd
    obtain ⟨e,he,rfl⟩ := hd
    exact mem_map_of_mem N.subtype e.property
  have hDN : D ≤ N := hDZ.trans (map_subtype_le (center N))
  have hcard : Nat.card D = p ^ primeRank p (center N) :=
    (card_map_of_injective hf).trans hEc
  have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join D (a : G)
    ((orderOf_injective P.subtype P.subtype_injective a).trans ha)
    (fun hd => haN (hDN hd)) (by
      intro d hd
      exact mem_centralizer_singleton_iff.mpr (hPZ a.property d (hDZ hd))) hcard
  omega

theorem IsNormalizerFrattiniIrreducible.le_normal_of_inner_of_exponent_p
    {P : Subgroup G} (hirr : IsNormalizerFrattiniIrreducible P)
    (hP : IsPGroup p P) (hp : Odd p) (hnc : ¬ IsCyclic P)
    (hexp : ∀ a : P, a ^ p = 1)
    (hr : primeRank p G ≤ 2) (N : Subgroup G) [N.Normal] [Group.IsPerfect N]
    (hinner : P ≤ N ⊔ centralizer (N : Set G)) (hmove : ⁅N,P⁆ ≠ ⊥) : P ≤ N := by
  by_contra hnot
  obtain ⟨a,haP,haN⟩ := Set.not_subset.mp hnot
  have hane : a ≠ 1 := fun he => haN (he.symm ▸ N.one_mem)
  have hao : orderOf (⟨a,haP⟩ : P) = p :=
    orderOf_eq_prime (hexp ⟨a,haP⟩) (fun he => hane (congrArg P.subtype he))
  have hZr := center_rank_of_escape P N hinner ⟨a,haP⟩ hao haN hr
  have hall : ∀ x : N, orderOf x = p → x ∈ center N := by
    intro x hx
    by_contra hn
    exact hnot (hirr.le_normal_of_inner_of_noncentral_prime hP hp hnc hr N hinner x hx hn)
  let S : Sylow p N := Classical.choice inferInstance
  have hScyc : IsCyclic S := S.isCyclic_of_odd_of_elementary_card_le hp (by
    intro E he
    let := he
    have hEZ : E ≤ center N := by
      intro x hx
      by_cases h1 : x = 1
      · exact h1.symm ▸ (center N).one_mem
      exact hall x (orderOf_eq_prime
        (elemPow_eq_one_of_isElementaryAbelian (p := p) x hx) h1)
    let D := E.subgroupOf (center N)
    let : IsElementaryAbelian p D := IsElementaryAbelian.subgroupOf hEZ
    have hDc : Nat.card D = Nat.card E := Nat.card_congr (subgroupOfEquivOfLe hEZ).toEquiv
    rw [← hDc]
    exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hZr D)
  let := hScyc
  have hZnot : ¬ p ∣ Nat.card (center N) := by
    have h := CentralExtension.not_dvd_card_kernel_of_commutative_sylow
      (QuotientGroup.mk' (center N)) (by rw [QuotientGroup.ker_mk']) S (by
        intro v hv w hw
        exact congrArg (S : Subgroup N).subtype
          (mul_comm (⟨v,hv⟩ : (S : Subgroup N)) ⟨w,hw⟩))
    simpa only [QuotientGroup.ker_mk'] using h
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p
    (prime_dvd_card_of_nontrivial_inner_pGroup hP N hinner hmove)
  exact hZnot (hx ▸ (center N).orderOf_dvd_natCard (hall x hx))
end Subgroup
