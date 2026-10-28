module

public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.Invariants
public import BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic.SplitIfs

/-!
# Scalar-invariant maps over ordinary Suzuki fields

A biadditive or triadditive map on a binary field of dimension at least four,
with values in any commutative group, vanishes if simultaneous multiplication
of all inputs by any nonzero scalar leaves its value unchanged.

Choose four linearly independent field elements and multiply the values over
all sixteen binary linear combinations. Expanding by additivity gives terms
involving at most three binary coordinates. Toggling an unused coordinate
pairs equal terms, whose product is one because every value has square one.
On the other hand, scalar invariance makes the original product the fifteenth
power of the desired value, hence that value itself. This proves vanishing
without imposing a linear structure or a finiteness assumption on the target.

The final two theorems instantiate exactly the predicates consumed by the
Suzuki central-defect argument, for the literal field of order `2^(2*m+1)`.
These are supporting mathematics for Aschbacher--Smith I.1.3 (printed p.407,
PDF p.418 of `refs/quasithin.pdf`) and GLS3 §6.1. They do not themselves assert
the multiplier theorem. The dimension bound excludes the exceptional field
of eight elements, where invariant triple maps need not vanish.
-/

public section
namespace ScalarInvariantMaps

open Finset Multiplicative

variable {C : Type*} [CommGroup C]

private lemma cube_prod (f : (Fin 4 → ZMod 2) → C) (l : Fin 4)
    (hf : ∀ v, f (Function.update v l (v l + 1)) = f v)
    (hsq : ∀ v, f v * f v = 1) : ∏ v, f v = 1 := by
  classical
  apply Finset.prod_ninvolution (fun v => Function.update v l (v l + 1))
  · intro v
    rw [hf, hsq]
  · intro v _ he
    have hh := congrFun he l
    simp at hh
  · intro v
    exact mem_univ _
  · intro v
    ext i
    by_cases hi : i = l
    · subst i
      simp [add_assoc, CharTwo.add_self_eq_zero]
    · simp [Function.update_of_ne hi]

private lemma unused (i j k : Fin 4) : ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  classical
  have hcard : ({i, j, k} : Finset (Fin 4)).card < (univ : Finset (Fin 4)).card := by
    have h := card_insert_le i ({j, k} : Finset (Fin 4))
    have h' := card_insert_le j ({k} : Finset (Fin 4))
    simp only [card_singleton, card_univ, Fintype.card_fin] at *
    omega
  obtain ⟨l, _, hl⟩ := exists_mem_notMem_of_card_lt_card hcard
  exact ⟨l, by simpa only [mem_insert, mem_singleton, not_or] using hl⟩

variable {F : Type*} [Field F] [CharP F 2]

private lemma hom_sq (f : Multiplicative F →* C) (x : F) :
    f (ofAdd x) * f (ofAdd x) = 1 := by
  rw [← map_mul]
  change f (ofAdd (x + x)) = 1
  simp [CharTwo.add_self_eq_zero]

private lemma triple_cube (b : Multiplicative F →* (Multiplicative F →*
    (Multiplicative F →* C))) (a : Fin 4 → F) (x y z : F)
    [Algebra (ZMod 2) F] :
    (∏ v : Fin 4 → ZMod 2,
      b (ofAdd ((∑ i, v i • a i) * x))
        (ofAdd ((∑ i, v i • a i) * y))
        (ofAdd ((∑ i, v i • a i) * z))) = 1 := by
  classical
  simp_rw [Finset.sum_mul, ofAdd_sum, map_prod]
  simp_rw [MonoidHom.finsetProd_apply]
  rw [Finset.prod_comm]
  apply Finset.prod_eq_one
  intro i _
  rw [Finset.prod_comm]
  apply Finset.prod_eq_one
  intro j _
  rw [Finset.prod_comm]
  apply Finset.prod_eq_one
  intro k _
  obtain ⟨l, hli, hlj, hlk⟩ := unused i j k
  apply cube_prod _ l
  · intro v
    simp [Ne.symm hli, Ne.symm hlj, Ne.symm hlk]
  · intro v
    exact hom_sq _ _

private lemma pairing_cube (b : Multiplicative F →* (Multiplicative F →* C))
    (a : Fin 4 → F) (x y : F) [Algebra (ZMod 2) F] :
    (∏ v : Fin 4 → ZMod 2,
      b (ofAdd ((∑ i, v i • a i) * x))
        (ofAdd ((∑ i, v i • a i) * y))) = 1 := by
  classical
  simp_rw [Finset.sum_mul, ofAdd_sum, map_prod, MonoidHom.finsetProd_apply]
  rw [Finset.prod_comm]
  apply Finset.prod_eq_one
  intro i _
  rw [Finset.prod_comm]
  apply Finset.prod_eq_one
  intro j _
  obtain ⟨l, hli, hlj, _⟩ := unused i j j
  apply cube_prod _ l
  · intro v
    simp [Ne.symm hli, Ne.symm hlj]
  · intro v
    exact hom_sq _ _

omit [CharP F 2] in
private lemma cube_invariant [Algebra (ZMod 2) F] (a : Fin 4 → F)
    (ha : LinearIndependent (ZMod 2) a) (f : F → C) (c : C)
    (hzero : f 0 = 1) (hf : ∀ t, t ≠ 0 → f t = c) :
    (∏ v : Fin 4 → ZMod 2, f (∑ i, v i • a i)) = c ^ 15 := by
  classical
  have hz (v : Fin 4 → ZMod 2) : (∑ i, v i • a i) = 0 ↔ v = 0 :=
    (Fintype.linearCombination (ZMod 2) a).map_eq_zero_iff
      ha.fintypeLinearCombination_injective
  calc
    _ = ∏ v : Fin 4 → ZMod 2, if v = 0 then 1 else c := by
      apply Finset.prod_congr rfl
      intro v _
      split_ifs with hv
      · simp [hv, hzero]
      · exact hf _ (mt (hz v).mp hv)
    _ = c ^ 15 := by
      simp [Finset.prod_ite, Finset.filter_ne', Fintype.card_pi, ZMod.card]

private lemma pow_fifteen (c : C) (hc : c * c = 1) : c ^ 15 = c := by
  change c ^ (2 * 7 + 1) = c
  rw [pow_add, pow_mul, pow_two, hc]
  simp

universe u v

/-- Scalar-invariant triple maps vanish in binary dimension at least four,
for commutative targets in any universe. -/
theorem triplesVanish_of_four_le_finrank (K : Type u) [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (hdim : 4 ≤ Module.finrank (ZMod 2) K) : ScalarInvariantMaps.TriplesVanish.{u, v} K := by
  classical
  obtain ⟨a, ha⟩ := exists_linearIndependent_of_le_finrank hdim
  intro C _ b hb
  apply MonoidHom.ext
  intro x
  apply MonoidHom.ext
  intro y
  apply MonoidHom.ext
  intro z
  change b x y z = 1
  have hc := triple_cube b a x.toAdd y.toAdd z.toAdd
  have he := cube_invariant a ha
    (fun t => b (ofAdd (t * x.toAdd)) (ofAdd (t * y.toAdd)) (ofAdd (t * z.toAdd)))
    (b x y z) (by simp) (by
      intro t ht
      exact hb (Units.mk0 t ht) x y z)
  have hs : b x y z * b x y z = 1 := by
    simpa only [ofAdd_toAdd] using hom_sq (b x y) z.toAdd
  rw [he, pow_fifteen _ hs] at hc
  exact hc

/-- Scalar-invariant pairings vanish in binary dimension at least four,
for commutative targets in any universe. -/
theorem pairingsVanish_of_four_le_finrank (K : Type u) [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (hdim : 4 ≤ Module.finrank (ZMod 2) K) : ScalarInvariantMaps.PairingsVanish.{u, v} K := by
  classical
  obtain ⟨a, ha⟩ := exists_linearIndependent_of_le_finrank hdim
  intro C _ b hb
  apply MonoidHom.ext
  intro x
  apply MonoidHom.ext
  intro y
  change b x y = 1
  have hc := pairing_cube b a x.toAdd y.toAdd
  have he := cube_invariant a ha
    (fun t => b (ofAdd (t * x.toAdd)) (ofAdd (t * y.toAdd)))
    (b x y) (by simp) (by
      intro t ht
      exact hb (Units.mk0 t ht) x y)
  have hs : b x y * b x y = 1 := by
    simpa only [ofAdd_toAdd] using hom_sq (b x) y.toAdd
  rw [he, pow_fifteen _ hs] at hc
  exact hc

end ScalarInvariantMaps

namespace BenderSuzuki.MatrixGroups.SchurCover.Family

universe v

open PFAppendixIII

/-- The pairing input for ordinary Suzuki root splitting, with no
invariant-vanishing premise. -/
theorem pairingsVanish (m : ℕ) (hm : 2 ≤ m) :
    ScalarInvariantMaps.PairingsVanish.{0, v} (BinaryGaloisField (2 * m + 1)) := by
  apply ScalarInvariantMaps.pairingsVanish_of_four_le_finrank
  rw [GaloisField.finrank 2 (by omega)]
  omega

/-- The triple-map input for ordinary Suzuki root splitting, with no
invariant-vanishing premise. -/
theorem triplesVanish (m : ℕ) (hm : 2 ≤ m) :
    ScalarInvariantMaps.TriplesVanish.{0, v} (BinaryGaloisField (2 * m + 1)) := by
  apply ScalarInvariantMaps.triplesVanish_of_four_le_finrank
  rw [GaloisField.finrank 2 (by omega)]
  omega

end BenderSuzuki.MatrixGroups.SchurCover.Family
end
