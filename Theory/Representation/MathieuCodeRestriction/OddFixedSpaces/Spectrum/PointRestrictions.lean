module

public import Theory.Mathieu.M24.Properties.Sylow3
public import Theory.Mathieu.M24.Properties.Transitivity
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Theory.GroupTheory.SylowElementConjugacy
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import all Theory.Mathieu.M24.Properties.Sylow3

/-!
# Native M₂₄ odd-prime point restrictions

This extension supplies the permutation-group input for the odd-prime spectrum.
The explicit Sylow-3 carrier from `Properties.Sylow3` is checked on all of its
27 coordinates; its nonidentity elements have support 24 or 18, so their
fixed-point sets have size 0 or 6.  For primes at least five, five-transitivity
computes every pointwise five-set fixer to have order 48, excluding an odd
prime subgroup that fixes five points.

The `import all` edge is intentional: the Sylow module keeps its coordinate
word evaluator private while publishing the subgroup and its cardinality.  This
extension consumes that checked evaluator without widening the stable public
boundary.  Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.15.7(1), printed pp.401–402, with the beta point-count input on p.396.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu
namespace MathieuCode

private theorem fixed_card_eq_sub_support (g : Equiv.Perm (Fin 24)) :
    Nat.card (Function.fixedPoints g) = 24 - g.support.card := by
  change Nat.card {x : Fin 24 | g x = x} = 24 - g.support.card
  rw [Nat.card_eq_fintype_card]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x => g x = x)
  change (Finset.univ.filter (fun x => g x = x)).card + g.support.card =
    (Finset.univ : Finset (Fin 24)).card at h
  simpa using Nat.eq_sub_of_add_eq h

private theorem sylow3_local_support : ∀ t : Fin 3 × Fin 3 × Fin 3,
    t ≠ (0, 0, 0) →
    ((Sporadic.Mathieu.evaluate t : Sporadic.Mathieu.M24) :
      Equiv.Perm (Fin 24)).support.card = 24 ∨
    ((Sporadic.Mathieu.evaluate t : Sporadic.Mathieu.M24) :
      Equiv.Perm (Fin 24)).support.card = 18 := by
  decide +kernel

private theorem sylow3_support_restriction (x : M24)
    (hx : x ∈ (Sporadic.Mathieu.m24Sylow3Subgroup : Subgroup M24))
    (hxne : x ≠ 1) :
    x.val.support.card = 24 ∨ x.val.support.card = 18 := by
  obtain ⟨t, rfl⟩ := hx
  apply sylow3_local_support t
  rintro rfl
  exact hxne Sporadic.Mathieu.evaluate_one

private theorem fixingSubgroup_card_of_five (S : Set (Fin 24)) (hS : S.ncard = 5) :
    Nat.card (fixingSubgroup M24 S) = 48 := by
  have ht : MulAction.IsMultiplyPretransitive M24 (Fin 24) S.ncard :=
    hS.symm ▸ m24_isFivePretransitive
  have hi := ht.index_of_fixingSubgroup_eq S
  rw [hS, Nat.card_fin] at hi
  norm_num [Nat.choose, Nat.factorial] at hi
  have hc := (fixingSubgroup M24 S).card_mul_index
  rw [hi, m24_order] at hc
  omega

private theorem fixed_points_of_order_three (D : Subgroup M24)
    (hD : Nat.card D = 3) :
    Nat.card (MulAction.fixedPoints D (Fin 24)) = 0 ∨
      Nat.card (MulAction.fixedPoints D (Fin 24)) = 6 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h] at hD
    simp at hD
  obtain ⟨x, hxD, hxne⟩ := D.bot_or_exists_ne_one.resolve_left hDne
  have hxorder : orderOf x = 3 := by
    apply orderOf_eq_prime
    · have hp := congrArg Subtype.val
        (pow_card_eq_one' (x := (⟨x, hxD⟩ : D)))
      simpa [hD] using hp
    · exact hxne
  let xd : D := ⟨x, hxD⟩
  have hxdne : xd ≠ 1 := by
    intro h
    exact hxne (congrArg Subtype.val h)
  have hfix : MulAction.fixedPoints D (Fin 24) =
      Function.fixedPoints (x : Equiv.Perm (Fin 24)) := by
    ext i
    constructor
    · intro hi
      exact hi xd
    · intro hi a
      exact smul_eq_self_of_mem_zpowers
        (mem_zpowers_of_prime_card hD hxdne) hi
  rw [hfix]
  let S : Sylow 3 M24 := Sporadic.Mathieu.m24Sylow3
  obtain ⟨y, hy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow
    (x := x) (n := 1) (by simpa using hxorder)
  have hyne : (y : M24) ≠ 1 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hy
    intro h
    apply hxne
    exact (MulAut.conj g).injective (hg.trans (h.trans (map_one _).symm))
  have hylocal : (y : M24) ∈ (Sporadic.Mathieu.m24Sylow3Subgroup : Subgroup M24) := by
    rw [← Sporadic.Mathieu.m24Sylow3_coe]
    exact y.property
  have hsupport := sylow3_support_restriction (y : M24) hylocal hyne
  have hconj : x.val.support.card = (y : M24).val.support.card := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hy
    rw [← hg]
    change x.val.support.card =
      ((g : Equiv.Perm (Fin 24)) * x.val * (g : Equiv.Perm (Fin 24))⁻¹).support.card
    exact (Equiv.Perm.card_support_conj (σ := (g : Equiv.Perm (Fin 24)))
      (τ := x.val)).symm
  rw [fixed_card_eq_sub_support]
  rcases hsupport with h | h <;> rw [hconj, h] at * <;> omega

private theorem fixed_points_le_four_of_prime_ge_five (D : Subgroup M24)
    {p : ℕ} (hp : p.Prime) (hD : Nat.card D = p) (hp5 : 5 ≤ p) :
    Nat.card (MulAction.fixedPoints D (Fin 24)) ≤ 4 := by
  by_contra hn
  have hfive : 5 ≤ Nat.card (MulAction.fixedPoints D (Fin 24)) := by omega
  have hset : (MulAction.fixedPoints D (Fin 24)).ncard =
      Nat.card (MulAction.fixedPoints D (Fin 24)) := by
    rw [Nat.card_coe_set_eq]
  obtain ⟨S, hSsub, hScard⟩ := Set.exists_subset_card_eq
    (s := MulAction.fixedPoints D (Fin 24))
    (n := 5) (hset ▸ hfive)
  have hle : D ≤ fixingSubgroup M24 S := by
    intro x hx
    rw [mem_fixingSubgroup_iff]
    intro i hi
    let xd : D := ⟨x, hx⟩
    exact hSsub hi xd
  have hdiv : p ∣ Nat.card (fixingSubgroup M24 S) := by
    simpa [hD] using (Subgroup.card_dvd_of_le hle)
  rw [fixingSubgroup_card_of_five S hScard] at hdiv
  change p ∣ 2 ^ 4 * 3 at hdiv
  rcases hp.dvd_mul.mp hdiv with htwo | hthree
  · have hle2 := Nat.le_of_dvd (by decide : 0 < 2) (hp.dvd_of_dvd_pow htwo)
    omega
  · have hle3 := Nat.le_of_dvd (by decide : 0 < 3) hthree
    omega

/-- Every odd-prime subgroup of the native M₂₄ action has the source point
restriction: cubic subgroups fix 0 or 6 points, while primes at least five fix
at most four points. -/
public theorem m24_odd_prime_point_restriction (D : Subgroup M24) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    (p = 3 ∧ (Nat.card (MulAction.fixedPoints D (Fin 24)) = 0 ∨
        Nat.card (MulAction.fixedPoints D (Fin 24)) = 6)) ∨
      (5 ≤ p ∧ Nat.card (MulAction.fixedPoints D (Fin 24)) ≤ 4) := by
  by_cases hp3 : p = 3
  · left
    have hD3 : Nat.card D = 3 := hp3 ▸ hD
    exact ⟨hp3, fixed_points_of_order_three D hD3⟩
  · right
    have hp5 : 5 ≤ p := by
      have hp2 := hp.two_le
      rcases ho with ⟨k, hk⟩
      omega
    exact ⟨hp5, fixed_points_le_four_of_prime_ge_five D hp hD hp5⟩

end MathieuCode
