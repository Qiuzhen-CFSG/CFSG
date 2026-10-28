module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankFixedJoin
/-!
# Order-three actors in the component reduction

A component with three-rank at least two in an overgroup of three-rank at
most two has centralizer of order prime to three when the overgroup has
trivial odd core. A Sylow three-subgroup supplies an elementary nine in
the component. Any centralizing element of order three would enlarge it
to an elementary twenty-seven; the component's two-group center excludes
the only possible overlap. We transport the intrinsic centralizer to
`I ∩ C_G(L)` by an actual multiplicative equivalence.

The identity `Y₊ = θ(M ∩ I)` supplies an order-three generator outside L
whenever Y₊ is not contained in L. Such a generator cannot act innerly:
writing it as `l c` would put `c³` in L, and coprimality of `|C_I(L)|`
with three then puts c, and hence the generator, in L. Conjugation on L
is constructed explicitly. For the perfect component with central two-core,
the same argument applies to the action on `L/O₂(L)`.

These deductions support the application of A.3.18 in 15.3.37 and 15.3.43.
They do not classify the outer action as linear or unitary diagonal; that
model-specific step, including the nonsplit branch of A.3.18(2), remains
part of the signed-model reduction.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.18
(printed pp.51--52), 15.3.11(6), 15.3.37 and 15.3.43 (pp.1135, 1139).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Candidates
variable {G : Type*} [Group G] [Finite G]

private theorem exists_elementaryNine_of_rank (h : 2 ≤ primeRank 3 G) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  classical
  let P : Sylow 3 G := Classical.choice inferInstance
  have hn : ¬ IsCyclic P := by
    intro hc
    have hr := P.primeRank_le_one_of_isCyclic hc
    omega
  obtain ⟨E, _, hcard, he⟩ :=
    P.isPGroup'.exists_normal_elementary_prime_sq_of_odd_not_isCyclic (by decide) hn
  let := he
  refine ⟨E.map (P : Subgroup G).subtype, IsElementaryAbelian.map_subtype, ?_⟩
  simpa only [Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective] using hcard

private theorem centralizer_three_coprime_of_rank {L : Subgroup G}
    (hcore : center L ≤ pCore 2 L) (hrankL : 2 ≤ primeRank 3 L)
    (hrankG : primeRank 3 G ≤ 2) :
    Nat.Coprime 3 (Nat.card (centralizer (L : Set G))) := by
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨A, hA, hAc⟩ := exists_elementaryNine_of_rank hrankL
  let := hA
  let E := A.map L.subtype
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.map_subtype
  have hEc : Nat.card E = 3 ^ 2 := by
    simpa only [E, Subgroup.card_map_of_injective L.subtype_injective] using hAc
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) 3 hd
  have hxG : orderOf (x : G) = 3 := (orderOf_injective (centralizer (L : Set G)).subtype Subtype.val_injective x).trans hx
  have hxL : (x : G) ∉ L := by
    intro hxL
    have hz : (⟨x, hxL⟩ : L) ∈ center L := by
      apply mem_center_iff.mpr
      intro l
      exact Subtype.ext (mem_centralizer_iff.mp x.property l l.property)
    have hp := (pCore_isPGroup (p := 2) (G := L)).orderOf_coprime
      (show Nat.Coprime 2 3 by decide) (⟨⟨x, hxL⟩, hcore hz⟩ : pCore 2 L)
    simp only [Subgroup.orderOf_mk, hxG] at hp
    norm_num at hp
  have hfix : E ≤ centralizer ({(x : G)} : Set G) := by
    intro e he
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp x.property e ((map_subtype_le A) he))
  have hb := IsElementaryAbelian.primeRank_ge_of_fixed_join E x hxG
    (fun he => hxL ((map_subtype_le A) he)) hfix hEc
  omega

omit [Finite G] in
private theorem order_three_mem_of_inner {I L : Subgroup G} {y : G}
    (hLI : L ≤ I) (hyI : y ∈ I) (hy3 : orderOf y = 3)
    (hC : Nat.Coprime 3 (Nat.card (I ⊓ centralizer (L : Set G) : Subgroup G)))
    (hinner : ∃ l ∈ L, l⁻¹ * y ∈ centralizer (L : Set G)) : y ∈ L := by
  obtain ⟨l, hl, hc⟩ := hinner
  let c := l⁻¹ * y
  have hcI : c ∈ I := I.mul_mem (I.inv_mem (hLI hl)) hyI
  have hcop : Nat.Coprime 3 (orderOf c) := by
    have hh := hC.of_dvd_right
      (orderOf_dvd_natCard (⟨c, hcI, hc⟩ : (I ⊓ centralizer (L : Set G) : Subgroup G)))
    rwa [← orderOf_injective (I ⊓ centralizer (L : Set G)).subtype Subtype.val_injective] at hh
  have hcomm : Commute l c := mem_centralizer_iff.mp hc l hl
  have hprod : l * c = y := by simp [c]
  have hpow : l ^ 3 * c ^ 3 = 1 := by
    rw [← hcomm.mul_pow, hprod, ← hy3, pow_orderOf_eq_one]
  have hc3 : c ^ 3 ∈ L := by
    have he : c ^ 3 = (l ^ 3)⁻¹ := by
      calc
        c ^ 3 = (l ^ 3)⁻¹ * (l ^ 3 * c ^ 3) := by group
        _ = (l ^ 3)⁻¹ := by rw [hpow, mul_one]
    rw [he]
    exact L.inv_mem (L.pow_mem hl 3)
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
  have hcL : c ∈ L := hn ▸ L.pow_mem hc3 n
  exact hprod ▸ L.mul_mem hl hcL


omit [Finite G] in
/-- The order-three generators of the actual local intersection witness noncontainment. -/
theorem exists_order_three_outside_of_local {Yplus M I L : Subgroup G}
    (hθ : theta (M ⊓ I) = Yplus) (hnot : ¬ Yplus ≤ L) :
    ∃ y ∈ Yplus, y ∈ M ⊓ I ∧ orderOf y = 3 ∧ y ∉ L := by
  have hgen : ∃ y ∈ M ⊓ I, orderOf y = 3 ∧ y ∉ L := by
    by_contra! hn
    apply hnot
    rw [← hθ]
    exact (closure_le _).mpr (fun y hy => hn y hy.1 hy.2)
  obtain ⟨y, hy, horder, hout⟩ := hgen
  exact ⟨y, hθ ▸ subset_closure ⟨hy, horder⟩, hy, horder, hout⟩

omit [Finite G] in
private theorem exists_outer_conjugation_of_not_inner {L : Subgroup G} {y : G}
    (hy : y ∈ normalizer (L : Set G))
    (hnot : ¬ ∃ l ∈ L, l⁻¹ * y ∈ centralizer (L : Set G)) :
    ∃ α : MulAut L, ConjugationOn L y α ∧ α ∉ MulAut.innerSubgroup L := by
  let α := L.normalizerMonoidHom ⟨y, hy⟩
  refine ⟨α, fun x => rfl, ?_⟩
  rintro ⟨l, hl⟩
  apply hnot
  refine ⟨l, l.property, ?_⟩
  apply mem_centralizer_iff.mpr
  intro x hx
  have he := congrArg (fun f : MulAut L => (f ⟨x, hx⟩ : G)) hl
  change (l : G) * x * (l : G)⁻¹ = y * x * y⁻¹ at he
  calc
    x * ((l : G)⁻¹ * y) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * y := by group
    _ = (l : G)⁻¹ * (y * x * y⁻¹) * y := by rw [he]
    _ = ((l : G)⁻¹ * y) * x := by group

omit [Finite G] in
/-- The local centralizer order makes an outside order-three generator an actual outer actor. -/
theorem exists_order_three_outer_of_local {Yplus M I L : Subgroup G}
    (hθ : theta (M ⊓ I) = Yplus) (hnot : ¬ Yplus ≤ L)
    (hLI : L ≤ I) (hnorm : Yplus ≤ normalizer (L : Set G))
    (hC : Nat.Coprime 3 (Nat.card (I ⊓ centralizer (L : Set G) : Subgroup G))) :
    ∃ y ∈ Yplus, orderOf y = 3 ∧ y ∉ L ∧
      ∃ α : MulAut L, ConjugationOn L y α ∧ α ∉ MulAut.innerSubgroup L := by
  obtain ⟨y, hy, hyMI, hy3, hyL⟩ := exists_order_three_outside_of_local hθ hnot
  refine ⟨y, hy, hy3, hyL, exists_outer_conjugation_of_not_inner (hnorm hy) ?_⟩
  exact fun hinner => hyL (order_three_mem_of_inner hLI hyMI.2 hy3 hC hinner)

omit [Finite G] in
/-- For the perfect component, the section-action kernel is the ordinary centralizer. -/
theorem not_section_inner_of_order_three_outside {I L : Subgroup G} {y : G}
    [Group.IsPerfect L] (hcore : pCore 2 L ≤ center L)
    (hLI : L ≤ I) (hyI : y ∈ I) (hy3 : orderOf y = 3) (hyL : y ∉ L)
    (hC : Nat.Coprime 3 (Nat.card (I ⊓ centralizer (L : Set G) : Subgroup G))) :
    ¬ ∃ l ∈ L, l⁻¹ * y ∈ Chapter4.sectionCentralizer L := by
  rw [sectionCentralizer_eq_centralizer_of_perfect hcore]
  exact fun hinner => hyL (order_three_mem_of_inner hLI hyI hy3 hC hinner)

/-- The full three-rank component has a three-prime centralizer in the actual overgroup I. -/
theorem local_centralizer_three_coprime {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2) :
    Nat.Coprime 3 (Nat.card (I ⊓ centralizer (L : Set G) : Subgroup G)) := by
  have hr : 2 ≤ primeRank 3 (L.subgroupOf I) := by
    rwa [primeRank_equiv 3 (subgroupOfEquivOfLe hLI)]
  have hc := centralizer_three_coprime_of_rank
    (component_center_eq_twoCore hcomp hodd).le hr hrankI
  let e : centralizer (L.subgroupOf I : Set I) ≃*
      (I ⊓ centralizer (L : Set G) : Subgroup G) := {
    toFun := fun x => ⟨x.1.1, x.1.2, fun l hl => congrArg Subtype.val
      (mem_centralizer_iff.mp x.2 (⟨l, hLI hl⟩ : I) hl)⟩
    invFun := fun x => ⟨⟨x.1, x.2.1⟩, fun l hl => Subtype.ext
      (mem_centralizer_iff.mp x.2.2 l hl)⟩
    left_inv := fun x => rfl
    right_inv := fun x => rfl
    map_mul' := fun x y => rfl }
  rwa [Nat.card_congr e.toEquiv] at hc

/-- The rank-two local hypotheses construct an order-three element and its outer conjugation action. -/
theorem exists_order_three_outer_of_rank_two {Yplus M I L : Subgroup G}
    (hθ : theta (M ⊓ I) = Yplus) (hnot : ¬ Yplus ≤ L)
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2) :
    ∃ y ∈ Yplus, orderOf y = 3 ∧ y ∉ L ∧
      ∃ α : MulAut L, ConjugationOn L y α ∧ α ∉ MulAut.innerSubgroup L := by
  have hYI : Yplus ≤ I := by
    rw [← hθ]
    exact (theta_le _).trans inf_le_right
  have hnorm := ComponentIntersection.normalizes_of_index_le_two hYI
    (hθ ▸ ComponentIntersection.theta_isPPerfect (M ⊓ I)) hindex
  exact exists_order_three_outer_of_local hθ hnot hLI hnorm
    (local_centralizer_three_coprime hLI hcomp hodd hrankL hrankI)

end CFSG.Quasithin.Chapter15.Section03.Candidates
