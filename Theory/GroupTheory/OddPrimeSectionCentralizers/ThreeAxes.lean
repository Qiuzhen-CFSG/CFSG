module
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer
public import Mathlib.GroupTheory.Exponent

/-!
# Three independent prime axes swapped by an involution

An involution swapping two axes of an embedded elementary abelian group of
order p³ centralizes a noncyclic subgroup of order p². The involution-centralizer
bound in rank-two sections excludes this configuration. The rank bound stays
on the original source of the surjection; no quotient-rank monotonicity is used.

Source: Aschbacher--Smith H.2, printed p.378, applying A.1.31(1).
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {K G C : Type*} [Group K] [Finite K] [Group G] [Finite G]
  [CommGroup C] [Finite C] {p : ℕ} [Fact p.Prime]

/-- The three-axis obstruction used in the unitary reflection argument.
Rank is retained on the actual source of the surjection. -/
theorem no_three_axes_swapped_in_rank_two_section
    (hp : Odd p) (f : K →* G) (hf : Function.Surjective f) (hrank : primeRank p K ≤ 2)
    (hc : Nat.card C = p) (j : (Fin 3 → C) →* G) (hj : Function.Injective j)
    (t : G) (ht : orderOf t = 2)
    (hswap : ∀ x, t * j x * t⁻¹ = j (x ∘ Equiv.swap (0 : Fin 3) 1)) : False := by
  let P := j.range
  have hPc : IsPGroup p C := IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hc)
  have hPi : IsPGroup p (Fin 3 → C) := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_fun,hc,Nat.card_fin])
  have hP : IsPGroup p P := hPi.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have htN : t ∈ normalizer (P : Set G) := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨a ∘ Equiv.swap 0 1,(hswap a).symm⟩
    · intro hx
      have htt : t*t=1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht).1
      have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right htt
      obtain ⟨a,ha⟩ := hx
      refine ⟨a ∘ Equiv.swap 0 1,?_⟩
      rw [←hswap,ha,hti]
      simp only [←mul_assoc,htt,one_mul]
      rw [mul_assoc,htt,mul_one]
  let H := P ⊔ zpowers t
  have hHN : H ≤ normalizer (P : Set G) := sup_le P.le_normalizer (zpowers_le.mpr htN)
  let P' := P.subgroupOf H
  let : P'.Normal := normal_subgroupOf_of_le_normalizer hHN
  let fH : H.comap f →* H := f.subgroupComap H
  have hfH : Function.Surjective fH := f.subgroupComap_surjective_of_surjective H hf
  let t' : H := ⟨t,(le_sup_right : zpowers t ≤ H) (mem_zpowers t)⟩
  have ht' : orderOf t' = 2 := (orderOf_injective H.subtype H.subtype_injective t').symm.trans ht
  have hcp : 1 < Nat.card C := hc ▸ (Fact.out : p.Prime).one_lt
  let : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp hcp
  obtain ⟨c,hc1⟩ := exists_ne (1 : C)
  have htmove : t' ∉ centralizer (P' : Set H) := by
    intro hcent
    let x : Fin 3 → C := ![c,1,1]
    have hx : j x ∈ P := ⟨x,rfl⟩
    have he : t * j x * t⁻¹ = j x := by
      have hh := congrArg Subtype.val (hcent ⟨j x,(le_sup_left : P ≤ H) hx⟩ hx)
      change j x * t = t * j x at hh
      rw [←hh,mul_assoc,mul_inv_cancel,mul_one]
    rw [hswap] at he
    have hh := congrFun (hj he) 0
    exact hc1 (by simpa [x] using hh.symm)
  let pair : C × C →* (Fin 3 → C) :=
    { toFun x := ![x.1,x.1,x.2]
      map_one' := by ext i; fin_cases i <;> rfl
      map_mul' := fun _ _ => by ext i; fin_cases i <;> rfl }
  let k : C × C →* H :=
    (j.comp pair).codRestrict H (fun x => (le_sup_left : P ≤ H) ⟨pair x,rfl⟩)
  have hk : Function.Injective k := by
    intro x y he
    have hh := hj (congrArg Subtype.val he)
    exact Prod.ext (congrFun hh 0) (congrFun hh 2)
  let R := k.range
  have hR : IsPGroup p R := (IsPGroup.of_card (n := 2) (show Nat.card (C × C) = p^2 by rw [Nat.card_prod,hc,pow_two])).of_surjective k.rangeRestrict k.rangeRestrict_surjective
  have hRt : R ≤ centralizer ({t'} : Set H) := by
    rintro _ ⟨x,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    have hh := hswap (pair x)
    have he : pair x ∘ Equiv.swap (0 : Fin 3) 1 = pair x := by
      ext i; fin_cases i <;> simp [pair, Equiv.swap_apply_def]
    rw [he] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hcyclic : IsCyclic R :=
    cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two hp fH hfH
      ((primeRank_subgroup_le p (H.comap f)).trans hrank) P'
      hP.comap_subtype t' ht' htmove R hR hRt
  let : IsCyclic (C × C) := isCyclic_of_injective k.rangeRestrict
    (fun _ _ he => hk (congrArg Subtype.val he))
  have hexp : Monoid.exponent (C × C) ∣ p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Prod.ext (by change x.1 ^ p = 1; simpa only [←hc] using pow_card_eq_one' (x := x.1))
        (by change x.2 ^ p = 1; simpa only [←hc] using pow_card_eq_one' (x := x.2)))
  rw [IsCyclic.exponent_eq_card,Nat.card_prod,hc] at hexp
  have hh := Nat.le_of_dvd (Fact.out : p.Prime).pos hexp
  have hp2 := (Fact.out : p.Prime).two_le
  nlinarith
end Theory.GroupTheory


