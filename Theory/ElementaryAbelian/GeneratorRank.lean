module

public import Theory.PrimeRank
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Generator rank of elementary abelian groups

A basis over `ZMod p` generates the underlying group. Counting the vector
space then bounds its generator rank and the generator ranks of its subgroups.
These bounds support concrete Sylow calculations, including the M22 three-rank
in Aschbacher–Smith, Lemma A.2.19 (printed p. 41).

The basis-to-generators argument is adapted from the existing
`FeitThompson/GeneratorRank.lean`, using `Group.rank` directly and only downward
imports so that intrinsic group calculations can reuse it.
-/

open scoped IsMulCommutative

namespace IsElementaryAbelian

/-- A vector-space basis generates the underlying elementary abelian group. -/
public theorem rank_le_finrank {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsElementaryAbelian p G] :
    Group.rank G ≤ Module.finrank (ZMod p) (Additive G) := by
  classical
  let b := Module.finBasis (ZMod p) (Additive G)
  let s : Fin (Module.finrank (ZMod p) (Additive G)) → G := fun i => Additive.toMul (b i)
  have hadd_top : AddSubgroup.closure (Set.range fun i => b i) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.toAddSubgroup_eq_top]
    have hsurj : Function.Surjective (algebraMap ℤ (ZMod p)) := by
      simpa using (ZMod.intCast_surjective (n := p))
    calc
      Submodule.span ℤ (Set.range fun i => b i)
          = (Submodule.span (ZMod p) (Set.range fun i => b i)).restrictScalars ℤ := by
              symm
              exact Submodule.restrictScalars_span ℤ (ZMod p) hsurj _
      _ = ⊤ := by simp [b.span_eq]
  have hgroup_top : Subgroup.closure (Set.range s) = ⊤ := by
    have hrange :
        Additive.ofMul ⁻¹' Set.range (fun i => b i) = Set.range s := by
      ext g
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, by simpa [s] using congrArg Additive.toMul hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, by simpa [s] using congrArg Additive.ofMul hi⟩
    calc
      Subgroup.closure (Set.range s)
          = (AddSubgroup.closure (Set.range fun i => b i)).toSubgroup' := by
              symm
              rw [AddSubgroup.toSubgroup'_closure, hrange]
      _ = ⊤ := by simp [hadd_top]
  let S : Finset G := Finset.univ.image s
  have hS_top : Subgroup.closure (S : Set G) = ⊤ := by
    simpa [S, Finset.coe_image, Finset.coe_univ, Set.image_univ] using hgroup_top
  exact (Group.rank_le hS_top).trans (by simpa [S] using Finset.card_image_le (f := s) (s := Finset.univ))

/-- Cardinality bounds the generator rank of an elementary abelian group. -/
public theorem rank_le_of_card_le {p n : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsElementaryAbelian p G]
    (hc : Nat.card G ≤ p ^ n) : Group.rank G ≤ n := by
  have hcard : Nat.card G = p ^ Module.finrank (ZMod p) (Additive G) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive G)
  exact (rank_le_finrank G).trans ((Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp (hcard ▸ hc))

/-- The same cardinality bound controls every subgroup, hence the prime rank. -/
public theorem primeRank_le_of_card_le {p n : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsElementaryAbelian p G]
    (hc : Nat.card G ≤ p ^ n) : primeRank p G ≤ n := by
  apply csSup_le'
  rintro k ⟨A, _, hAc, _, hk⟩
  let : IsMulCommutative A := hAc
  let : IsElementaryAbelian p A := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p G) x.val) }
  exact hk.trans (rank_le_of_card_le A (A.card_le_card_group.trans hc))
end IsElementaryAbelian

