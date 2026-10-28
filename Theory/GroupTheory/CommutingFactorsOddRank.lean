module

public import Theory.GroupTheory.PrimeRankWitness
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Odd rank from commuting factors with two-group centers

Choose a cyclic subgroup of the same odd prime order in each factor. The
other factors centralize the chosen factor, so any intersection with their
join lies in its center. A two-group center meets an odd-order cyclic group
trivially. Multiplication therefore embeds the product of these cyclic
groups, giving the claimed lower bound on prime rank.

This is the elementary rank argument used for the conjugate families in
Aschbacher–Smith, combined manuscript (1 March 2004), E.6.22–23, printed
pp.254–255 (PDF pp.265–266). No component or block classification is needed.
-/

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

/-- Commuting factors with two-group centers contribute independent odd
prime-order cyclic subgroups to the ambient prime rank. -/
public theorem Subgroup.card_le_primeRank_of_commuting_factors {I : Type*} [Fintype I]
    (D : I → Subgroup G) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hc : Pairwise fun i j => D i ≤ centralizer (D j : Set G))
    (hz : ∀ i, IsPGroup 2 (center (D i)))
    (x : ∀ i, D i) (hx : ∀ i, orderOf (x i) = p) :
    Fintype.card I ≤ primeRank p G := by
  classical
  let E : I → Subgroup G := fun i => zpowers (x i : G)
  have hED (i : I) : E i ≤ D i := zpowers_le.mpr (x i).property
  have hxG (i : I) : orderOf (x i : G) = p :=
    (orderOf_injective (D i).subtype Subtype.val_injective (x i)).trans (hx i)
  let (i : I) : IsElementaryAbelian p (E i) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hxG i ▸ pow_orderOf_eq_one (x i : G))
  have hind : iSupIndep E := by
    rw [iSupIndep_def]
    intro i
    apply disjoint_def.mpr
    intro a ha hi
    have hothers : (⨆ j, ⨆ (_ : j ≠ i), E j) ≤ centralizer (D i : Set G) :=
      iSup_le fun j => iSup_le fun hji => (hED j).trans (hc hji)
    have haZ : (⟨a, hED i ha⟩ : D i) ∈ center (D i) := by
      apply mem_center_iff.mpr
      intro d
      exact Subtype.ext (mem_centralizer_iff.mp (hothers hi) d d.property)
    let z : center (D i) := ⟨⟨a, hED i ha⟩, haZ⟩
    have hzp : z ^ p = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      change a ^ p = 1
      exact congrArg Subtype.val
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p (E i)) ⟨a, ha⟩)
    have hz1 : z = 1 := by
      apply orderOf_eq_one_iff.mp
      obtain ⟨n, hn⟩ := (hz i).exists_orderOf_dvd_pow z
      exact Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_right.mpr ho).pow_right n)
        (orderOf_dvd_of_pow_eq_one hzp) hn
    exact congrArg (fun z : center (D i) => ((z : D i) : G)) hz1
  have hcomm : Pairwise fun i j : I => ∀ a b : G,
      a ∈ E i → b ∈ E j → Commute a b := by
    intro i j hij a b ha hb
    exact (mem_centralizer_iff.mp (hc hij (hED i ha)) b (hED j hb)).symm
  let f := Subgroup.noncommPiCoprod hcomm
  have hf : Function.Injective f := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  let (i : I) : CommGroup (E i) := IsMulCommutative.instCommGroup
  apply primeRank_ge_of_elementary_embedding (f := f) (hf := hf)
  · intro a
    funext i
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (E i)) (a i)
  · simp only [Nat.card_pi, E, Nat.card_zpowers, hxG, Finset.prod_const,
      Finset.card_univ]

