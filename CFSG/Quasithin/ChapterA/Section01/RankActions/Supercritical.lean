module

public import CFSG.Quasithin.ChapterA.Section01.PStructure
public import Theory.GroupTheory.PGroup.SupercriticalSmallRank
public import Theory.GroupTheory.PGroup.SupercriticalAutomorphisms

/-!
# Small-rank supercritical models

Rank at most one forces a cyclic supercritical subgroup, whose exponent
and nontriviality give order p. At rank two the class-two omega theorem
A.1.24 supplies the actual elementary or Heisenberg isomorphism.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.25(1), printed p.25. The printed model list omits the trivial ambient
group; the model theorem therefore states nontriviality explicitly, while
the imported rank equality applies to all finite odd p-groups of rank ≤ 2.
-/

namespace CFSG.Quasithin.ChapterA

/-- A.1.25(1): each supercritical subgroup has the ambient prime rank and
is cyclic of order p, an elementary plane, or the exponent-p extraspecial
group of order p³. The nontriviality assumption is necessary for the printed
three alternatives; `primeRank_eq_of_le_two` also handles P = 1. -/
public theorem lemma_A_1_25_1
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P] [Nontrivial P]
    (hp : Odd p) (hP : IsPGroup p P) (hr : primeRank p P ≤ 2)
    (X : Subgroup P) (hX : IsSupercriticalPSubgroup p X) :
    primeRank p X = primeRank p P ∧
      ((Nat.card X = p ∧ Nonempty (X ≃* Multiplicative (ZMod p))) ∨
       (Nat.card X = p ^ 2 ∧
         Nonempty (X ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))) ∨
       (Nat.card X = p ^ 3 ∧ IsExtraspecial p X ∧
         Nonempty (X ≃* HeisenbergPrime p))) := by
  have heq := hX.primeRank_eq_of_le_two hP hp hr
  refine ⟨heq, ?_⟩
  by_cases htwo : primeRank p X = 2
  · exact Or.inr (lemma_A_1_24 (by rintro rfl; obtain ⟨k, hk⟩ := hp; omega)
      (hP.to_subgroup X) hX.omega₁_eq_top hX.derived_le_center htwo)
  · have hxle : primeRank p X ≤ 1 := by omega
    let : IsCyclic X := (hP.to_subgroup X).isCyclic_of_odd_of_elementary_card_le hp
      (fun E hE => by
        let : IsElementaryAbelian p E := hE
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hxle E)
    let : Nontrivial X := hX.nontrivial_of_nontrivial hP
    have hc : Nat.card X = p := by
      rw [← IsCyclic.exponent_eq_card]
      exact ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ hX.exponent_dvd_p).resolve_left
        (Nat.ne_of_gt Monoid.one_lt_exponent)
    exact Or.inl ⟨hc, ⟨mulEquivOfPrimeCardEq hc (by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p),
        Nat.card_zmod])⟩⟩

open Subgroup

/-- The supercritical Frattini quotient in A.1.25 has order at most p².
The trivial ambient group is included. This is the dimension bound needed
for the actual two-dimensional automorphism representation. -/
public theorem lemma_A_1_25_frattini_card
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hp : Odd p) (hP : IsPGroup p P) (hr : primeRank p P ≤ 2)
    (X : Subgroup P) (hX : IsSupercriticalPSubgroup p X) :
    Nat.card (X ⧸ frattini X) ≤ p ^ 2 := by
  cases subsingleton_or_nontrivial P with
  | inl hs =>
    let : Subsingleton P := hs
    let : Subsingleton (X ⧸ frattini X) :=
      Function.Surjective.subsingleton (QuotientGroup.mk'_surjective (frattini X))
    have hc : Nat.card (X ⧸ frattini X) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    rw [hc]
    have hpos := (Fact.out : p.Prime).pos
    exact Nat.one_le_pow _ _ hpos
  | inr hn =>
    let : Nontrivial P := hn
    have hm := (lemma_A_1_25_1 hp hP hr X hX).2
    have hle := Nat.le_of_dvd (Nat.card_pos (α := X))
      (card_quotient_dvd_card (frattini X))
    rcases hm with hcyc | hplane | ⟨hcard, hextra, _⟩
    · have hpos := (Fact.out : p.Prime).pos
      rw [hcyc.1] at hle
      nlinarith
    · exact hle.trans_eq hplane.1
    · let : IsExtraspecial p X := hextra
      have hphi : Nat.card (frattini X) = p := by
        rw [IsExtraspecial.frattini_eq_center (p := p), IsExtraspecial.center_order_p p X]
      have hprod := (frattini X).index_mul_card
      change Nat.card (X ⧸ frattini X) * Nat.card (frattini X) = Nat.card X at hprod
      rw [hphi, hcard, show 3 = 2 + 1 from rfl, pow_succ] at hprod
      exact (mul_right_cancel₀ (Fact.out : p.Prime).ne_zero hprod).le

end CFSG.Quasithin.ChapterA
