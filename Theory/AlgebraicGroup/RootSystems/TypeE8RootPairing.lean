module

public import Mathlib.LinearAlgebra.Matrix.Dual
public import Theory.AlgebraicGroup.RootSystems.Exceptional
public meta import Mathlib.Data.Fintype.Pi
public meta import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# The standard root pairing of type E8

This module equips the 240 roots in `StandardRootSystem.typeE8Roots` with the Euclidean
root-coroot pairing.  Every root has squared length two, so roots and coroots use the same
coordinate embedding.  Reflection stability is checked directly for the pair-root and
even-parity half-sign families; finite integer certificates then give crystallographicity.
Thus the construction uses only the coordinate model from `Exceptional.lean`, not the
classification of semisimple groups or a Chevalley existence theorem.

The corrected eight displayed simple roots are proved linearly independent and every root
or its negative is expressed with natural coefficients in them.  They therefore form a
base.  The exported `Fin 8` numbering identifies its Cartan matrix with
`typeE8CartanMatrix`, whose explicit connected graph proves irreducibility.  Together with
the common root norm, this also supplies the finite, crystallographic, reduced root-system
instances required by later E8 constructions.
-/

namespace Theory.AlgebraicGroup.StandardRootSystem

open Set

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

private def e8Sign (ε : Fin 8 → Bool) (i : Fin 8) : ℤ :=
  if ε i then 1 else -1

private def e8EvenNegative (ε : Fin 8 → Bool) : Prop :=
  (Finset.univ.filter fun i => !(ε i)).card % 2 = 0

private lemma evenNegative_iff_e8EvenNegative (ε : Fin 8 → Bool) :
    evenNegative ε ↔ e8EvenNegative ε := by
  exact Nat.even_iff

set_option maxRecDepth 100000 in
private theorem e8EvenNegative_iff_sign_prod_one (ε : Fin 8 → Bool) :
    e8EvenNegative ε ↔ ∏ i, e8Sign ε i = 1 := by
  unfold e8EvenNegative
  decide +revert

private lemma e8Sign_not (ε : Fin 8 → Bool) (i : Fin 8) :
    e8Sign (fun j => !(ε j)) i = -e8Sign ε i := by
  cases h : ε i <;> norm_num [e8Sign, h]

private theorem evenNegative_not (ε : Fin 8 → Bool) (hε : evenNegative ε) :
    evenNegative (fun i => !(ε i)) := by
  rw [evenNegative_iff_e8EvenNegative] at hε ⊢
  rw [e8EvenNegative_iff_sign_prod_one] at hε ⊢
  calc
    ∏ i, e8Sign (fun j => !(ε j)) i = ∏ i, -e8Sign ε i := by
      apply Finset.prod_congr rfl
      intro i _
      exact e8Sign_not ε i
    _ = ∏ i, e8Sign ε i := by simp only [Fin.prod_univ_eight]; ring
    _ = 1 := hε

private theorem evenNegative_swap (a b : Fin 8) (ε : Fin 8 → Bool)
    (hε : evenNegative ε) :
    evenNegative (fun i => ε (Equiv.swap a b i)) := by
  rw [evenNegative_iff_e8EvenNegative] at hε ⊢
  rw [e8EvenNegative_iff_sign_prod_one] at hε ⊢
  change (∏ i, e8Sign ε (Equiv.swap a b i)) = 1
  calc
    ∏ i, e8Sign ε (Equiv.swap a b i) = ∏ i, e8Sign ε i :=
      Equiv.prod_comp (Equiv.swap a b) (e8Sign ε)
    _ = 1 := hε

private theorem evenNegative_swap_not_two (a b : Fin 8) (hab : a ≠ b)
    (ε : Fin 8 → Bool) (hε : evenNegative ε) :
    evenNegative (fun i =>
      if i = a ∨ i = b then !(ε (Equiv.swap a b i)) else ε i) := by
  rw [evenNegative_iff_e8EvenNegative] at hε ⊢
  rw [e8EvenNegative_iff_sign_prod_one] at hε ⊢
  let η : Fin 8 → Bool := fun i => ε (Equiv.swap a b i)
  have hη : (∏ i, e8Sign η i) = 1 := by
    change (∏ i, e8Sign ε (Equiv.swap a b i)) = 1
    calc
      ∏ i, e8Sign ε (Equiv.swap a b i) = ∏ i, e8Sign ε i :=
        Equiv.prod_comp (Equiv.swap a b) (e8Sign ε)
      _ = 1 := hε
  have hpoint (i : Fin 8) :
      e8Sign (fun i =>
          if i = a ∨ i = b then !(ε (Equiv.swap a b i)) else ε i) i =
        (if i ∈ ({a, b} : Finset (Fin 8)) then (-1 : ℤ) else 1) * e8Sign η i := by
    by_cases hia : i = a
    · subst i
      simp [η, e8Sign, hab]
      cases ε b <;> rfl
    · by_cases hib : i = b
      · subst i
        simp [η, e8Sign, hia]
        cases ε a <;> rfl
      · have hswap : Equiv.swap a b i = i := Equiv.swap_apply_of_ne_of_ne hia hib
        simp [η, e8Sign, hia, hib, hswap]
  have hfactor :
      (∏ i, if i ∈ ({a, b} : Finset (Fin 8)) then (-1 : ℤ) else 1) = 1 := by
    rw [Finset.prod_ite_mem_eq]
    simp [hab]
  calc
    ∏ i, e8Sign (fun i =>
        if i = a ∨ i = b then !(ε (Equiv.swap a b i)) else ε i) i =
        ∏ i, ((if i ∈ ({a, b} : Finset (Fin 8)) then (-1 : ℤ) else 1) *
          e8Sign η i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact hpoint i
    _ = (∏ i, if i ∈ ({a, b} : Finset (Fin 8)) then (-1 : ℤ) else 1) *
          ∏ i, e8Sign η i := Finset.prod_mul_distrib
    _ = 1 := by rw [hfactor, hη]; norm_num

private def e8Agreement (ε δ : Fin 8 → Bool) (i : Fin 8) : Bool :=
  ε i == δ i

private lemma e8Sign_agreement (ε δ : Fin 8 → Bool) (i : Fin 8) :
    e8Sign (e8Agreement ε δ) i = e8Sign ε i * e8Sign δ i := by
  cases hε : ε i <;> cases hδ : δ i <;> simp [e8Agreement, e8Sign, hε, hδ]

private lemma e8Agreement_eq_false_iff (ε δ : Fin 8 → Bool) (i : Fin 8) :
    e8Agreement ε δ i = false ↔ ε i ≠ δ i := by
  cases hε : ε i <;> cases hδ : δ i <;> simp [e8Agreement, hε, hδ]

private lemma e8Agreement_eq_true_iff (ε δ : Fin 8 → Bool) (i : Fin 8) :
    e8Agreement ε δ i = true ↔ ε i = δ i := by
  cases hε : ε i <;> cases hδ : δ i <;> simp [e8Agreement, hε, hδ]

private theorem e8EvenNegative_agreement (ε δ : Fin 8 → Bool)
    (hε : e8EvenNegative ε) (hδ : e8EvenNegative δ) :
    e8EvenNegative (e8Agreement ε δ) := by
  rw [e8EvenNegative_iff_sign_prod_one] at hε hδ ⊢
  calc
    ∏ i, e8Sign (e8Agreement ε δ) i =
        ∏ i, (e8Sign ε i * e8Sign δ i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact e8Sign_agreement ε δ i
    _ = (∏ i, e8Sign ε i) * ∏ i, e8Sign δ i := Finset.prod_mul_distrib
    _ = 1 := by rw [hε, hδ]; norm_num

set_option maxRecDepth 100000 in
private theorem e8Sign_sum_cases_single (ε : Fin 8 → Bool)
    (hε : e8EvenNegative ε) :
    (∑ i, e8Sign ε i) = -8 ∨ (∑ i, e8Sign ε i) = -4 ∨
      (∑ i, e8Sign ε i) = 0 ∨ (∑ i, e8Sign ε i) = 4 ∨
        (∑ i, e8Sign ε i) = 8 := by
  unfold e8EvenNegative at hε
  decide +revert

set_option maxRecDepth 100000 in
private theorem e8Sign_sum_eq_neg_eight_single (ε : Fin 8 → Bool)
    (h : (∑ i, e8Sign ε i) = -8) : ∀ i, ε i = false := by
  decide +revert

set_option maxRecDepth 100000 in
private theorem e8Sign_sum_eq_eight_single (ε : Fin 8 → Bool)
    (h : (∑ i, e8Sign ε i) = 8) : ∀ i, ε i = true := by
  decide +revert

set_option maxRecDepth 100000 in
private theorem e8Sign_sum_eq_four_single (ε : Fin 8 → Bool)
    (h : (∑ i, e8Sign ε i) = 4) :
    ∃ a b : Fin 8, a ≠ b ∧ ∀ i, (i = a ∨ i = b) ↔ ε i = false := by
  decide +revert

set_option maxRecDepth 100000 in
private theorem e8Sign_sum_eq_neg_four_single (ε : Fin 8 → Bool)
    (h : (∑ i, e8Sign ε i) = -4) :
    ∃ a b : Fin 8, a ≠ b ∧ ∀ i, (i = a ∨ i = b) ↔ ε i = true := by
  decide +revert

private lemma e8Sign_sum_agreement (ε δ : Fin 8 → Bool) :
    (∑ i, e8Sign (e8Agreement ε δ) i) =
      ∑ i, e8Sign ε i * e8Sign δ i := by
  apply Finset.sum_congr rfl
  intro i _
  exact e8Sign_agreement ε δ i

private theorem e8Sign_sum_cases (ε δ : Fin 8 → Bool)
    (hε : evenNegative ε) (hδ : evenNegative δ) :
    (∑ i, e8Sign ε i * e8Sign δ i) = -8 ∨
      (∑ i, e8Sign ε i * e8Sign δ i) = -4 ∨
      (∑ i, e8Sign ε i * e8Sign δ i) = 0 ∨
      (∑ i, e8Sign ε i * e8Sign δ i) = 4 ∨
      (∑ i, e8Sign ε i * e8Sign δ i) = 8 := by
  rw [evenNegative_iff_e8EvenNegative] at hε hδ
  have h := e8Sign_sum_cases_single (e8Agreement ε δ)
    (e8EvenNegative_agreement ε δ hε hδ)
  rwa [e8Sign_sum_agreement] at h

private theorem e8Sign_sum_eq_neg_eight (ε δ : Fin 8 → Bool)
    (h : (∑ i, e8Sign ε i * e8Sign δ i) = -8) :
    ∀ i, ε i ≠ δ i := by
  have hs : (∑ i, e8Sign (e8Agreement ε δ) i) = -8 := by
    rwa [e8Sign_sum_agreement]
  intro i
  rw [← e8Agreement_eq_false_iff]
  exact e8Sign_sum_eq_neg_eight_single (e8Agreement ε δ) hs i

private theorem e8Sign_sum_eq_eight (ε δ : Fin 8 → Bool)
    (h : (∑ i, e8Sign ε i * e8Sign δ i) = 8) : ε = δ := by
  have hs : (∑ i, e8Sign (e8Agreement ε δ) i) = 8 := by
    rwa [e8Sign_sum_agreement]
  funext i
  rw [← e8Agreement_eq_true_iff]
  exact e8Sign_sum_eq_eight_single (e8Agreement ε δ) hs i

private theorem e8Sign_sum_eq_four (ε δ : Fin 8 → Bool)
    (h : (∑ i, e8Sign ε i * e8Sign δ i) = 4) :
    ∃ a b : Fin 8, a ≠ b ∧ ∀ i, (i = a ∨ i = b) ↔ ε i ≠ δ i := by
  have hs : (∑ i, e8Sign (e8Agreement ε δ) i) = 4 := by
    rwa [e8Sign_sum_agreement]
  obtain ⟨a, b, hab, hiff⟩ :=
    e8Sign_sum_eq_four_single (e8Agreement ε δ) hs
  exact ⟨a, b, hab, fun i => (hiff i).trans (e8Agreement_eq_false_iff ε δ i)⟩

private theorem e8Sign_sum_eq_neg_four (ε δ : Fin 8 → Bool)
    (h : (∑ i, e8Sign ε i * e8Sign δ i) = -4) :
    ∃ a b : Fin 8, a ≠ b ∧ ∀ i, (i = a ∨ i = b) ↔ ε i = δ i := by
  have hs : (∑ i, e8Sign (e8Agreement ε δ) i) = -4 := by
    rwa [e8Sign_sum_agreement]
  obtain ⟨a, b, hab, hiff⟩ :=
    e8Sign_sum_eq_neg_four_single (e8Agreement ε δ) hs
  exact ⟨a, b, hab, fun i => (hiff i).trans (e8Agreement_eq_true_iff ε δ i)⟩

private lemma dot_add_left_E8 (x y z : Vec 8) :
    dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

private lemma dot_add_right_E8 (x y z : Vec 8) :
    dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

private lemma dot_sub_left_E8 (x y z : Vec 8) :
    dot (x - y) z = dot x z - dot y z := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

private lemma dot_smul_left_E8 (c : ℝ) (x y : Vec 8) :
    dot (c • x) y = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma dot_smul_right_E8 (c : ℝ) (x y : Vec 8) :
    dot x (c • y) = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma dot_basisVector_basisVector_E8 (i j : Fin 8) :
    dot (basisVector i) (basisVector j) = if i = j then 1 else 0 := by
  classical
  simp [dot, basisVector, Pi.single_apply, eq_comm]

private lemma dot_basisVector_left_E8 (i : Fin 8) (x : Vec 8) :
    dot (basisVector i) x = x i := by
  classical
  simp [dot, basisVector, Pi.single_apply]

private lemma dot_basisVector_right_E8 (x : Vec 8) (i : Fin 8) :
    dot x (basisVector i) = x i := by
  rw [dot_comm, dot_basisVector_left_E8]

private lemma pairVector_apply_E8 (s t : ℝ) (a b : Fin 8) (hab : a ≠ b) (i : Fin 8) :
    (s • basisVector a + t • basisVector b : Vec 8) i =
      if i = a then s else if i = b then t else 0 := by
  classical
  by_cases hia : i = a
  · subst i
    simp [basisVector, hab, hab.symm]
  · by_cases hib : i = b
    · subst i
      simp [basisVector, hia]
    · simp [basisVector, hia, hib, Ne.symm hia, Ne.symm hib]

private lemma halfSignVector_eq_sign (ε : Fin 8 → Bool) (i : Fin 8) :
    halfSignVector ε i = (e8Sign ε i : ℝ) / 2 := by
  cases h : ε i <;> norm_num [halfSignVector, e8Sign, h]

private lemma halfSignVector_dot (ε δ : Fin 8 → Bool) :
    dot (halfSignVector ε) (halfSignVector δ) =
      ((∑ i, e8Sign ε i * e8Sign δ i : ℤ) : ℝ) / 4 := by
  simp only [dot]
  calc
    (∑ i, halfSignVector ε i * halfSignVector δ i) =
        ∑ i, ((e8Sign ε i * e8Sign δ i : ℤ) : ℝ) / 4 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [halfSignVector_eq_sign, halfSignVector_eq_sign]
      push_cast
      ring
    _ = ((∑ i, e8Sign ε i * e8Sign δ i : ℤ) : ℝ) / 4 := by
      rw [Int.cast_sum, Finset.sum_div]

private lemma halfSignVector_dot_cases (ε δ : Fin 8 → Bool)
    (hε : evenNegative ε) (hδ : evenNegative δ) :
    dot (halfSignVector ε) (halfSignVector δ) = -2 ∨
      dot (halfSignVector ε) (halfSignVector δ) = -1 ∨
      dot (halfSignVector ε) (halfSignVector δ) = 0 ∨
      dot (halfSignVector ε) (halfSignVector δ) = 1 ∨
      dot (halfSignVector ε) (halfSignVector δ) = 2 := by
  rw [halfSignVector_dot]
  rcases e8Sign_sum_cases ε δ hε hδ with h | h | h | h | h <;>
    rw [h] <;> norm_num

public theorem typeE8Roots_finite : typeE8Roots.Finite := by
  have hD : (typeDRoots 8).Finite := Set.finite_coe_iff.mp
    (Finite.of_surjective (typeDRootEmbedding 8) (typeDRootEmbedding_surjective 8))
  have hPair : (pairRoots 8).Finite := by simpa [typeDRoots] using hD
  have hHalf : ({x | ∃ ε : Fin 8 → Bool,
      evenNegative ε ∧ x = halfSignVector ε} : Set (Vec 8)).Finite :=
    (Set.finite_range halfSignVector).subset (by
      rintro _ ⟨ε, _, rfl⟩
      exact ⟨ε, rfl⟩)
  rw [typeE8Roots]
  exact hPair.union hHalf

public instance typeE8Roots_finiteType : Finite typeE8Roots :=
  Set.finite_coe_iff.mpr typeE8Roots_finite

@[expose] public noncomputable def typeE8RootEmbedding : typeE8Roots ↪ Vec 8 :=
  Function.Embedding.subtype _

@[simp] public lemma typeE8RootEmbedding_apply (r : typeE8Roots) :
    typeE8RootEmbedding r = (r : Vec 8) := rfl

public lemma typeE8Root_dot_self (r : typeE8Roots) : dot r.1 r.1 = 2 := by
  classical
  rcases r.2 with hrPair | ⟨ε, _, hr⟩
  · rcases hrPair with ⟨i, j, hij, s, t, hs, ht, hroot⟩
    rw [hroot]
    simp only [dot_add_left_E8, dot_add_right_E8, dot_smul_left_E8,
      dot_smul_right_E8, dot_basisVector_basisVector_E8]
    rcases hs with (rfl | rfl) <;> rcases ht with (rfl | rfl)
    all_goals norm_num [hij, hij.symm]
  · rw [hr, halfSignVector_dot]
    have hsquare (i : Fin 8) : e8Sign ε i * e8Sign ε i = 1 := by
      cases h : ε i <;> norm_num [e8Sign, h]
    simp_rw [hsquare]
    norm_num

public noncomputable def typeE8CoordinatePairing :
    Vec 8 →ₗ[ℝ] Vec 8 →ₗ[ℝ] ℝ :=
  (dotProductEquiv ℝ (Fin 8)).toLinearMap

public instance typeE8CoordinatePairing_isPerfPair :
    typeE8CoordinatePairing.IsPerfPair := by
  unfold typeE8CoordinatePairing
  infer_instance

public lemma typeE8CoordinatePairing_apply (x y : Vec 8) :
    typeE8CoordinatePairing x y = dot x y := by
  simp [typeE8CoordinatePairing, dotProductEquiv, dot, dotProduct]

private def typeE8HalfRoots : Set (Vec 8) :=
  {x | ∃ ε : Fin 8 → Bool, evenNegative ε ∧ x = halfSignVector ε}

private lemma typeE8Roots_eq :
    typeE8Roots = pairRoots 8 ∪ typeE8HalfRoots := rfl

private lemma typeE8HalfRoots_neg_mem {x : Vec 8} (hx : x ∈ typeE8HalfRoots) :
    -x ∈ typeE8HalfRoots := by
  rcases hx with ⟨ε, hε, rfl⟩
  refine ⟨fun i => !(ε i), evenNegative_not ε hε, ?_⟩
  ext i
  cases h : ε i <;> norm_num [halfSignVector, h]

private lemma pairRoot_dot_halfSignVector_cases (r : Vec 8)
    (hr : r ∈ pairRoots 8) (ε : Fin 8 → Bool) :
    dot r (halfSignVector ε) = -1 ∨
      dot r (halfSignVector ε) = 0 ∨
      dot r (halfSignVector ε) = 1 := by
  classical
  rcases hr with ⟨a, b, hab, s, t, hs, ht, rfl⟩
  simp only [dot_add_left_E8, dot_smul_left_E8, dot_basisVector_left_E8]
  rcases hs with (rfl | rfl) <;> rcases ht with (rfl | rfl) <;>
    cases ha : ε a <;> cases hb : ε b <;>
    norm_num [halfSignVector, ha, hb]

private lemma typeE8PairRoot_reflection_half_mapsTo :
    ∀ r ∈ pairRoots 8,
      MapsTo (fun x => x - dot r x • r) typeE8HalfRoots typeE8HalfRoots := by
  classical
  have hdiff_maps (a b : Fin 8) (hab : a ≠ b) :
      MapsTo (fun x => x - dot (basisVector a - basisVector b) x •
        (basisVector a - basisVector b)) typeE8HalfRoots typeE8HalfRoots := by
    rintro _ ⟨ε, hε, rfl⟩
    let ε' : Fin 8 → Bool := fun j => ε (Equiv.swap a b j)
    refine ⟨ε', evenNegative_swap a b ε hε, ?_⟩
    have hdot : dot (basisVector a - basisVector b) (halfSignVector ε) =
        halfSignVector ε a - halfSignVector ε b := by
      rw [dot_sub_left_E8, dot_basisVector_left_E8, dot_basisVector_left_E8]
    change halfSignVector ε -
        dot (basisVector a - basisVector b) (halfSignVector ε) •
          (basisVector a - basisVector b) = halfSignVector ε'
    rw [hdot]
    ext j
    by_cases hja : j = a
    · subst j
      cases ha : ε a <;> cases hb : ε b <;>
        simp [ε', halfSignVector, basisVector, hab, ha, hb]
    · by_cases hjb : j = b
      · subst j
        cases ha : ε a <;> cases hb : ε b <;>
          simp [ε', halfSignVector, basisVector, hja, ha, hb]
      · have hswap : Equiv.swap a b j = j :=
          Equiv.swap_apply_of_ne_of_ne hja hjb
        simp [ε', halfSignVector, basisVector, hja, hjb, hswap]
  have hsum_maps (a b : Fin 8) (hab : a ≠ b) :
      MapsTo (fun x => x - dot (basisVector a + basisVector b) x •
        (basisVector a + basisVector b)) typeE8HalfRoots typeE8HalfRoots := by
    rintro _ ⟨ε, hε, rfl⟩
    let ε' : Fin 8 → Bool := fun j =>
      if j = a ∨ j = b then !(ε (Equiv.swap a b j)) else ε j
    refine ⟨ε', evenNegative_swap_not_two a b hab ε hε, ?_⟩
    have hdot : dot (basisVector a + basisVector b) (halfSignVector ε) =
        halfSignVector ε a + halfSignVector ε b := by
      rw [dot_add_left_E8, dot_basisVector_left_E8, dot_basisVector_left_E8]
    change halfSignVector ε -
        dot (basisVector a + basisVector b) (halfSignVector ε) •
          (basisVector a + basisVector b) = halfSignVector ε'
    rw [hdot]
    ext j
    by_cases hja : j = a
    · subst j
      cases ha : ε a <;> cases hb : ε b <;>
        simp [ε', halfSignVector, basisVector, hab, ha, hb]
    · by_cases hjb : j = b
      · subst j
        cases ha : ε a <;> cases hb : ε b <;>
          simp [ε', halfSignVector, basisVector, hja, ha, hb]
      · simp [ε', halfSignVector, basisVector, hja, hjb]
  have hreflect_neg (r x : Vec 8) :
      x - dot (-r) x • (-r) = x - dot r x • r := by
    have hdot : dot (-r) x = -dot r x := by
      simp [dot, Finset.sum_neg_distrib]
    rw [hdot]
    module
  intro r hr
  rcases hr with ⟨a, b, hab, s, t, hs, ht, rfl⟩
  rcases hs with (rfl | rfl) <;> rcases ht with (rfl | rfl)
  · simp only [one_smul, neg_smul]
    rw [show -basisVector a + -basisVector b = -(basisVector a + basisVector b) by module]
    intro x hx
    change x - dot (-(basisVector a + basisVector b)) x •
      (-(basisVector a + basisVector b)) ∈ typeE8HalfRoots
    rw [hreflect_neg]
    exact hsum_maps a b hab hx
  · simp only [one_smul, neg_smul]
    rw [show -basisVector a + basisVector b = -(basisVector a - basisVector b) by module]
    intro x hx
    change x - dot (-(basisVector a - basisVector b)) x •
      (-(basisVector a - basisVector b)) ∈ typeE8HalfRoots
    rw [hreflect_neg]
    exact hdiff_maps a b hab hx
  · simpa only [one_smul, neg_smul, sub_eq_add_neg] using hdiff_maps a b hab
  · simpa only [one_smul] using hsum_maps a b hab

private lemma typeE8HalfRoot_reflection_pair_mapsTo :
    ∀ r ∈ typeE8HalfRoots,
      MapsTo (fun x => x - dot r x • r) (pairRoots 8) typeE8Roots := by
  rw [typeE8Roots_eq]
  intro r hr x hx
  rcases hr with ⟨ε, hε, rfl⟩
  have hd := pairRoot_dot_halfSignVector_cases x hx ε
  have hreflect := typeE8PairRoot_reflection_half_mapsTo x hx
    (show halfSignVector ε ∈ typeE8HalfRoots from ⟨ε, hε, rfl⟩)
  change halfSignVector ε - dot x (halfSignVector ε) • x ∈ typeE8HalfRoots at hreflect
  change x - dot (halfSignVector ε) x • halfSignVector ε ∈
    pairRoots 8 ∪ typeE8HalfRoots
  rw [dot_comm]
  rcases hd with hd | hd | hd
  · right
    simpa [hd, add_comm] using hreflect
  · left
    simpa [hd] using hx
  · right
    have hneg := typeE8HalfRoots_neg_mem hreflect
    simpa [hd] using hneg

private lemma typeE8HalfRoot_reflection_half_mapsTo :
    ∀ r ∈ typeE8HalfRoots,
      MapsTo (fun x => x - dot r x • r) typeE8HalfRoots typeE8Roots := by
  rw [typeE8Roots_eq]
  rintro _ ⟨ε, hε, rfl⟩ _ ⟨δ, hδ, rfl⟩
  rcases halfSignVector_dot_cases ε δ hε hδ with hd | hd | hd | hd | hd
  · have hsum : (∑ i, e8Sign ε i * e8Sign δ i) = -8 := by
      rw [halfSignVector_dot] at hd
      have hc : (((∑ i, e8Sign ε i * e8Sign δ i : ℤ) : ℝ)) = -8 := by linarith
      exact_mod_cast hc
    have hne := e8Sign_sum_eq_neg_eight ε δ hsum
    right
    refine ⟨ε, hε, ?_⟩
    change halfSignVector δ -
      dot (halfSignVector ε) (halfSignVector δ) • halfSignVector ε =
        halfSignVector ε
    rw [hd]
    ext i
    have hi := hne i
    cases hεi : ε i <;> cases hδi : δ i <;>
      simp_all [halfSignVector] <;> norm_num
  · have hsum : (∑ i, e8Sign ε i * e8Sign δ i) = -4 := by
      rw [halfSignVector_dot] at hd
      have hc : (((∑ i, e8Sign ε i * e8Sign δ i : ℤ) : ℝ)) = -4 := by linarith
      exact_mod_cast hc
    rcases e8Sign_sum_eq_neg_four ε δ hsum with ⟨a, b, hab, heq⟩
    left
    refine ⟨a, b, hab, (e8Sign δ a : ℝ), (e8Sign δ b : ℝ), ?_, ?_, ?_⟩
    · cases h : δ a <;> simp [e8Sign, h]
    · cases h : δ b <;> simp [e8Sign, h]
    · change halfSignVector δ -
        dot (halfSignVector ε) (halfSignVector δ) • halfSignVector ε = _
      rw [hd]
      ext i
      rw [pairVector_apply_E8 _ _ _ _ hab]
      by_cases hia : i = a
      · subst i
        have hi := (heq a).mp (Or.inl rfl)
        cases hεa : ε a <;> cases hδa : δ a <;>
          simp_all [halfSignVector, e8Sign, hab, hab.symm] <;> norm_num
      · by_cases hib : i = b
        · subst i
          have hi := (heq b).mp (Or.inr rfl)
          cases hεb : ε b <;> cases hδb : δ b <;>
            simp_all [halfSignVector, e8Sign, hab, hab.symm, hia] <;> norm_num
        · have hi : ε i ≠ δ i := by
            intro hieq
            have hmem := (heq i).mpr hieq
            exact hmem.elim hia hib
          cases hεi : ε i <;> cases hδi : δ i <;>
            simp_all [halfSignVector, e8Sign, hia, hib] <;> norm_num
  · right
    change halfSignVector δ -
      dot (halfSignVector ε) (halfSignVector δ) • halfSignVector ε ∈
        typeE8HalfRoots
    rw [hd]
    exact ⟨δ, hδ, by module⟩
  · have hsum : (∑ i, e8Sign ε i * e8Sign δ i) = 4 := by
      rw [halfSignVector_dot] at hd
      have hc : (((∑ i, e8Sign ε i * e8Sign δ i : ℤ) : ℝ)) = 4 := by linarith
      exact_mod_cast hc
    rcases e8Sign_sum_eq_four ε δ hsum with ⟨a, b, hab, hne⟩
    left
    refine ⟨a, b, hab, (e8Sign δ a : ℝ), (e8Sign δ b : ℝ), ?_, ?_, ?_⟩
    · cases h : δ a <;> simp [e8Sign, h]
    · cases h : δ b <;> simp [e8Sign, h]
    · change halfSignVector δ -
        dot (halfSignVector ε) (halfSignVector δ) • halfSignVector ε = _
      rw [hd]
      ext i
      rw [pairVector_apply_E8 _ _ _ _ hab]
      by_cases hia : i = a
      · subst i
        have hi := (hne a).mp (Or.inl rfl)
        cases hεa : ε a <;> cases hδa : δ a <;>
          simp_all [halfSignVector, e8Sign, hab, hab.symm] <;> norm_num
      · by_cases hib : i = b
        · subst i
          have hi := (hne b).mp (Or.inr rfl)
          cases hεb : ε b <;> cases hδb : δ b <;>
            simp_all [halfSignVector, e8Sign, hab, hab.symm, hia] <;> norm_num
        · have hi : ε i = δ i := by
            by_contra hneq
            have hmem := (hne i).mpr hneq
            simpa [hia, hib] using hmem
          cases hεi : ε i <;> cases hδi : δ i <;>
            simp_all [halfSignVector, e8Sign, hia, hib] <;> norm_num
  · have hsum : (∑ i, e8Sign ε i * e8Sign δ i) = 8 := by
      rw [halfSignVector_dot] at hd
      have hc : (((∑ i, e8Sign ε i * e8Sign δ i : ℤ) : ℝ)) = 8 := by linarith
      exact_mod_cast hc
    have heq := e8Sign_sum_eq_eight ε δ hsum
    subst δ
    right
    have hneg := typeE8HalfRoots_neg_mem
      (show halfSignVector ε ∈ typeE8HalfRoots from ⟨ε, hε, rfl⟩)
    change halfSignVector ε -
      dot (halfSignVector ε) (halfSignVector ε) • halfSignVector ε ∈
        typeE8HalfRoots
    rw [hd]
    convert hneg using 1 <;> module

public lemma typeE8Root_reflection_mapsTo :
    ∀ r ∈ typeE8Roots,
      MapsTo (fun x => x - dot r x • r) typeE8Roots typeE8Roots := by
  rw [typeE8Roots_eq]
  intro r hr x hx
  rcases hr with hrPair | hrHalf <;> rcases hx with hxPair | hxHalf
  · left
    exact (typeDRoot_reflection_mapsTo 8 r hrPair) hxPair
  · right
    exact typeE8PairRoot_reflection_half_mapsTo r hrPair hxHalf
  · exact typeE8HalfRoot_reflection_pair_mapsTo r hrHalf hxPair
  · exact typeE8HalfRoot_reflection_half_mapsTo r hrHalf hxHalf

public lemma typeE8Root_preReflection_mapsTo (r : typeE8Roots) :
    MapsTo
      (Module.preReflection (typeE8RootEmbedding r)
        (typeE8CoordinatePairing.flip (typeE8RootEmbedding r)))
      (range typeE8RootEmbedding) (range typeE8RootEmbedding) := by
  rintro _ ⟨s, rfl⟩
  have hmem := (typeE8Root_reflection_mapsTo r.1 r.2) s.2
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [Module.preReflection_apply]
  simp only [typeE8RootEmbedding_apply]
  change s.1 - dot r.1 s.1 • r.1 =
    s.1 - typeE8CoordinatePairing s.1 r.1 • r.1
  rw [typeE8CoordinatePairing_apply, dot_comm]

public lemma typeE8RootEmbedding_span_eq_top :
    Submodule.span ℝ (range typeE8RootEmbedding) = ⊤ := by
  have hD : Submodule.span ℝ (range (fun r : TypeDRootIndex 8 =>
      (typeDRootEmbedding 8 r : Vec 8))) = ⊤ := by
    simpa using typeDRootEmbedding_span_eq_top 6
  apply le_antisymm le_top
  calc
    ⊤ = Submodule.span ℝ (range (fun r : TypeDRootIndex 8 =>
        (typeDRootEmbedding 8 r : Vec 8))) := hD.symm
    _ ≤ Submodule.span ℝ (range typeE8RootEmbedding) :=
      Submodule.span_mono (by
        rintro x ⟨r, rfl⟩
        refine ⟨⟨(typeDRootEmbedding 8 r : Vec 8), Or.inl ?_⟩, rfl⟩
        exact (typeDRootEmbedding 8 r).property)

/-- The Euclidean root-coroot pairing on the standard 240-element E8 root set. -/
@[expose] public noncomputable def typeE8RootPairing :
    RootPairing typeE8Roots ℝ (Vec 8) (Vec 8) :=
  RootPairing.mk'' typeE8CoordinatePairing typeE8RootEmbedding typeE8RootEmbedding
    (fun r => by rw [typeE8CoordinatePairing_apply]; exact typeE8Root_dot_self r)
    typeE8Root_preReflection_mapsTo typeE8RootEmbedding_span_eq_top

@[simp] public lemma typeE8RootPairing_root (r : typeE8Roots) :
    typeE8RootPairing.root r = r.1 := rfl

@[simp] public lemma typeE8RootPairing_coroot (r : typeE8Roots) :
    typeE8RootPairing.coroot r = r.1 := rfl

@[simp] public lemma typeE8RootPairing_pairing (r s : typeE8Roots) :
    typeE8RootPairing.pairing r s = dot r.1 s.1 := by
  exact typeE8CoordinatePairing_apply _ _

public lemma typeE8RootPairing_pairing_eq_intCast (r s : typeE8Roots) :
    ∃ z : ℤ, (z : ℝ) = typeE8RootPairing.pairing r s := by
  classical
  have int_cases (x : ℝ)
      (hx : x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2) :
      ∃ z : ℤ, (z : ℝ) = x := by
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨-2, by norm_num⟩
    · exact ⟨-1, by norm_num⟩
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
  rw [typeE8RootPairing_pairing]
  rcases r.2 with hrPair | ⟨ε, hε, hr⟩ <;>
    rcases s.2 with hsPair | ⟨δ, hδ, hs⟩
  · let rr : typeDRoots 8 := ⟨r.1, hrPair⟩
    let ss : typeDRoots 8 := ⟨s.1, hsPair⟩
    obtain ⟨ri, hri⟩ := typeDRootEmbedding_surjective 8 rr
    obtain ⟨si, hsi⟩ := typeDRootEmbedding_surjective 8 ss
    have hval : ∃ z : ℤ, (z : ℝ) = (typeDRootPairing 6).pairing ri si :=
      RootPairing.exists_value ri si
    obtain ⟨z, hz⟩ := hval
    refine ⟨z, ?_⟩
    rw [typeDRootPairing_pairing] at hz
    have hri' : (typeDRootEmbedding 8 ri : Vec 8) = r.1 :=
      congrArg Subtype.val hri
    have hsi' : (typeDRootEmbedding 8 si : Vec 8) = s.1 :=
      congrArg Subtype.val hsi
    simpa [hri', hsi', dot_comm] using hz
  · rw [hs]
    rcases pairRoot_dot_halfSignVector_cases r.1 hrPair δ with h | h | h
    · exact int_cases _ (Or.inr (Or.inl h))
    · exact int_cases _ (Or.inr (Or.inr (Or.inl h)))
    · exact int_cases _ (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rw [hr, dot_comm]
    rcases pairRoot_dot_halfSignVector_cases s.1 hsPair ε with h | h | h
    · exact int_cases _ (Or.inr (Or.inl h))
    · exact int_cases _ (Or.inr (Or.inr (Or.inl h)))
    · exact int_cases _ (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rw [hr, hs]
    exact int_cases _ (halfSignVector_dot_cases ε δ hε hδ)

public instance typeE8RootPairing_isCrystallographic :
    typeE8RootPairing.IsCrystallographic := by
  constructor
  exact typeE8RootPairing_pairing_eq_intCast

public instance typeE8RootPairing_isRootSystem : typeE8RootPairing.IsRootSystem := by
  unfold typeE8RootPairing
  apply RootPairing.isRootSystem_mk''
  exact typeE8RootPairing_pairing_eq_intCast

private lemma dot_smul_self_E8 (c : ℝ) (x : Vec 8) :
    dot (c • x) (c • x) = c ^ 2 * dot x x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

public instance typeE8RootPairing_isReduced : typeE8RootPairing.IsReduced := by
  constructor
  intro r s hdep
  have hsmul := typeE8RootPairing.pairing_smul_root_eq_of_not_linearIndependent hdep
  simp only [typeE8RootPairing_root] at hsmul
  change typeE8RootPairing.pairing s r • r.1 = (2 : ℝ) • s.1 at hsmul
  have hnorm := congrArg (fun x : Vec 8 => dot x x) hsmul
  rw [dot_smul_self_E8, dot_smul_self_E8,
    typeE8Root_dot_self, typeE8Root_dot_self] at hnorm
  have hc : typeE8RootPairing.pairing s r = 2 ∨
      typeE8RootPairing.pairing s r = -2 := by
    apply eq_or_eq_neg_of_sq_eq_sq
    norm_num at hnorm ⊢
    nlinarith
  rcases hc with hc | hc
  · left
    rw [hc] at hsmul
    exact (isUnit_iff_ne_zero.mpr (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hsmul
  · right
    rw [hc] at hsmul
    have hneg : (2 : ℝ) • (-r.1) = (2 : ℝ) • s.1 := by
      rw [smul_neg, ← neg_smul]
      exact hsmul
    exact neg_eq_iff_eq_neg.mp
      ((isUnit_iff_ne_zero.mpr (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hneg)

@[expose] public noncomputable def typeE8SimpleRootIndex (i : Fin 8) : typeE8Roots :=
  ⟨typeE8SimpleRoot i, typeE8SimpleRoot_mem_typeE8Roots i⟩

@[simp] public lemma typeE8SimpleRootIndex_val (i : Fin 8) :
    (typeE8SimpleRootIndex i : Vec 8) = typeE8SimpleRoot i := rfl

public lemma typeE8SimpleRoots_linearIndependent :
    LinearIndependent ℝ typeE8SimpleRoot := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congrFun hg (0 : Fin 8)
  have h1 := congrFun hg (1 : Fin 8)
  have h2 := congrFun hg (2 : Fin 8)
  have h3 := congrFun hg (3 : Fin 8)
  have h4 := congrFun hg (4 : Fin 8)
  have h5 := congrFun hg (5 : Fin 8)
  have h6 := congrFun hg (6 : Fin 8)
  have h7 := congrFun hg (7 : Fin 8)
  simp [typeE8SimpleRoot, Fin.sum_univ_eight] at h0 h1 h2 h3 h4 h5 h6 h7
  have hg0 : g 0 = 0 := by linarith
  have hg1 : g 1 = 0 := by linarith
  have hg2 : g 2 = 0 := by linarith
  have hg3 : g 3 = 0 := by linarith
  have hg4 : g 4 = 0 := by linarith
  have hg5 : g 5 = 0 := by linarith
  have hg6 : g 6 = 0 := by linarith
  have hg7 : g 7 = 0 := by linarith
  fin_cases i <;> assumption

public lemma typeE8SimpleRootIndex_injective :
    Function.Injective typeE8SimpleRootIndex := by
  intro i j h
  apply typeE8SimpleRoots_linearIndependent.injective
  exact congrArg Subtype.val h

public lemma typeE8RootPairing_linearIndepOn_simpleRoots :
    LinearIndepOn ℝ typeE8RootPairing.root (Set.range typeE8SimpleRootIndex) := by
  rw [linearIndepOn_range_iff typeE8SimpleRootIndex_injective]
  simpa [Function.comp_def] using typeE8SimpleRoots_linearIndependent

@[expose] public noncomputable def typeE8SimpleCoefficient (x : Vec 8) : Fin 8 → ℝ
  | ⟨0, _⟩ => 2 * x 0
  | ⟨1, _⟩ => (7 * x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 - x 7) / 2
  | ⟨2, _⟩ => 5 * x 0 + x 1 + x 2 + x 3 + x 4 + x 5
  | ⟨3, _⟩ => (5 * x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7) / 2
  | ⟨4, _⟩ => 4 * x 0 + x 1 + x 2 + x 3 + x 4
  | ⟨5, _⟩ => 3 * x 0 + x 1 + x 2 + x 3
  | ⟨6, _⟩ => 2 * x 0 + x 1 + x 2
  | ⟨7, _⟩ => x 0 + x 1

public lemma typeE8SimpleCoefficient_reconstruction (x : Vec 8) :
    (∑ i, typeE8SimpleCoefficient x i • typeE8SimpleRoot i) = x := by
  funext i
  fin_cases i <;>
    norm_num [typeE8SimpleCoefficient, typeE8SimpleRoot, Fin.sum_univ_eight] <;>
      ring_nf <;>
      congr

private lemma dot_vec_eight
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℝ) :
    dot ![a0, a1, a2, a3, a4, a5, a6, a7]
        ![b0, b1, b2, b3, b4, b5, b6, b7] =
      a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 +
        a4 * b4 + a5 * b5 + a6 * b6 + a7 * b7 := by
  simp only [dot, Fin.sum_univ_eight]
  rfl

public lemma typeE8SimpleRoot_pairing (i j : Fin 8) :
    dot (typeE8SimpleRoot i) (typeE8SimpleRoot j) =
      (typeE8CartanMatrix i j : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [typeE8CartanMatrix, typeE8SimpleRoot, dot_vec_eight]

public lemma typeE8RootPairing_simpleIndex_pairing (i j : Fin 8) :
    typeE8RootPairing.pairing (typeE8SimpleRootIndex i) (typeE8SimpleRootIndex j) =
      algebraMap ℤ ℝ (typeE8CartanMatrix i j) := by
  rw [typeE8RootPairing_pairing]
  exact typeE8SimpleRoot_pairing i j

private def e8HalfCoefficientDenominator : Fin 8 → ℤ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 2
  | ⟨5, _⟩ => 2
  | ⟨6, _⟩ => 2
  | ⟨7, _⟩ => 2

private def e8HalfCoefficientNumerator (ε : Fin 8 → Bool) : Fin 8 → ℤ
  | ⟨0, _⟩ => e8Sign ε 0
  | ⟨1, _⟩ => 7 * e8Sign ε 0 + e8Sign ε 1 + e8Sign ε 2 + e8Sign ε 3 +
      e8Sign ε 4 + e8Sign ε 5 + e8Sign ε 6 - e8Sign ε 7
  | ⟨2, _⟩ => 5 * e8Sign ε 0 + e8Sign ε 1 + e8Sign ε 2 + e8Sign ε 3 +
      e8Sign ε 4 + e8Sign ε 5
  | ⟨3, _⟩ => 5 * e8Sign ε 0 + e8Sign ε 1 + e8Sign ε 2 + e8Sign ε 3 +
      e8Sign ε 4 + e8Sign ε 5 + e8Sign ε 6 + e8Sign ε 7
  | ⟨4, _⟩ => 4 * e8Sign ε 0 + e8Sign ε 1 + e8Sign ε 2 + e8Sign ε 3 +
      e8Sign ε 4
  | ⟨5, _⟩ => 3 * e8Sign ε 0 + e8Sign ε 1 + e8Sign ε 2 + e8Sign ε 3
  | ⟨6, _⟩ => 2 * e8Sign ε 0 + e8Sign ε 1 + e8Sign ε 2
  | ⟨7, _⟩ => e8Sign ε 0 + e8Sign ε 1

set_option maxRecDepth 100000 in
private theorem e8HalfCoefficient_nat_or_neg (ε : Fin 8 → Bool)
    (hε : evenNegative ε) :
    (∀ i, e8HalfCoefficientNumerator ε i = e8HalfCoefficientDenominator i *
        (Int.toNat (e8HalfCoefficientNumerator ε i / e8HalfCoefficientDenominator i) : ℤ)) ∨
      (∀ i, -e8HalfCoefficientNumerator ε i = e8HalfCoefficientDenominator i *
        (Int.toNat (-e8HalfCoefficientNumerator ε i / e8HalfCoefficientDenominator i) : ℤ)) := by
  rw [evenNegative_iff_e8EvenNegative] at hε
  unfold e8EvenNegative at hε
  decide +revert

private lemma halfSignVector_apply_eq_e8Sign (ε : Fin 8 → Bool) (i : Fin 8) :
    halfSignVector ε i = (e8Sign ε i : ℝ) / 2 := by
  cases h : ε i <;> norm_num [halfSignVector, e8Sign, h]

private lemma typeE8SimpleCoefficient_halfSignVector_scaled
    (ε : Fin 8 → Bool) (i : Fin 8) :
    (e8HalfCoefficientDenominator i : ℝ) *
        typeE8SimpleCoefficient (halfSignVector ε) i =
      (e8HalfCoefficientNumerator ε i : ℝ) := by
  fin_cases i <;>
    simp only [e8HalfCoefficientDenominator, e8HalfCoefficientNumerator,
      typeE8SimpleCoefficient, halfSignVector_apply_eq_e8Sign] <;>
    push_cast <;>
    ring

private lemma typeE8SimpleCoefficient_neg (x : Vec 8) (i : Fin 8) :
    typeE8SimpleCoefficient (-x) i = -typeE8SimpleCoefficient x i := by
  fin_cases i <;> simp [typeE8SimpleCoefficient] <;> ring

private lemma typeE8SimpleCoefficient_halfSignVector_eq_nat
    (ε : Fin 8 → Bool) (i : Fin 8) (n : ℕ)
    (h : e8HalfCoefficientNumerator ε i =
      e8HalfCoefficientDenominator i * (n : ℤ)) :
    typeE8SimpleCoefficient (halfSignVector ε) i = n := by
  have hs := typeE8SimpleCoefficient_halfSignVector_scaled ε i
  have hR := congrArg (fun z : ℤ => (z : ℝ)) h
  fin_cases i <;>
    norm_num [e8HalfCoefficientDenominator] at hs hR ⊢ <;>
    linarith

private lemma typeE8SimpleCoefficient_neg_halfSignVector_eq_nat
    (ε : Fin 8 → Bool) (i : Fin 8) (n : ℕ)
    (h : -e8HalfCoefficientNumerator ε i =
      e8HalfCoefficientDenominator i * (n : ℤ)) :
    typeE8SimpleCoefficient (-halfSignVector ε) i = n := by
  rw [typeE8SimpleCoefficient_neg]
  have hs := typeE8SimpleCoefficient_halfSignVector_scaled ε i
  have hR := congrArg (fun z : ℤ => (z : ℝ)) h
  fin_cases i <;>
    norm_num [e8HalfCoefficientDenominator] at hs hR ⊢ <;>
    linarith

private def e8BoolSign (b : Bool) : ℤ := if b then 1 else -1

private def e8PairCoordinate (i j : Fin 8) (a b : Bool) (k : Fin 8) : ℤ :=
  (if k = i then e8BoolSign a else 0) + (if k = j then e8BoolSign b else 0)

private def e8PairCoefficientDenominator : Fin 8 → ℤ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 1
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1

private def e8PairCoefficientNumerator (i j : Fin 8) (a b : Bool) : Fin 8 → ℤ
  | ⟨0, _⟩ => 2 * e8PairCoordinate i j a b 0
  | ⟨1, _⟩ => 7 * e8PairCoordinate i j a b 0 + e8PairCoordinate i j a b 1 +
      e8PairCoordinate i j a b 2 + e8PairCoordinate i j a b 3 +
      e8PairCoordinate i j a b 4 + e8PairCoordinate i j a b 5 +
      e8PairCoordinate i j a b 6 - e8PairCoordinate i j a b 7
  | ⟨2, _⟩ => 5 * e8PairCoordinate i j a b 0 + e8PairCoordinate i j a b 1 +
      e8PairCoordinate i j a b 2 + e8PairCoordinate i j a b 3 +
      e8PairCoordinate i j a b 4 + e8PairCoordinate i j a b 5
  | ⟨3, _⟩ => 5 * e8PairCoordinate i j a b 0 + e8PairCoordinate i j a b 1 +
      e8PairCoordinate i j a b 2 + e8PairCoordinate i j a b 3 +
      e8PairCoordinate i j a b 4 + e8PairCoordinate i j a b 5 +
      e8PairCoordinate i j a b 6 + e8PairCoordinate i j a b 7
  | ⟨4, _⟩ => 4 * e8PairCoordinate i j a b 0 + e8PairCoordinate i j a b 1 +
      e8PairCoordinate i j a b 2 + e8PairCoordinate i j a b 3 +
      e8PairCoordinate i j a b 4
  | ⟨5, _⟩ => 3 * e8PairCoordinate i j a b 0 + e8PairCoordinate i j a b 1 +
      e8PairCoordinate i j a b 2 + e8PairCoordinate i j a b 3
  | ⟨6, _⟩ => 2 * e8PairCoordinate i j a b 0 + e8PairCoordinate i j a b 1 +
      e8PairCoordinate i j a b 2
  | ⟨7, _⟩ => e8PairCoordinate i j a b 0 + e8PairCoordinate i j a b 1

set_option maxRecDepth 100000 in
private theorem e8PairCoefficient_nat_or_neg (i j : Fin 8) (a b : Bool)
    (hij : i ≠ j) :
    (∀ k, e8PairCoefficientNumerator i j a b k = e8PairCoefficientDenominator k *
        (Int.toNat (e8PairCoefficientNumerator i j a b k /
          e8PairCoefficientDenominator k) : ℤ)) ∨
      (∀ k, -e8PairCoefficientNumerator i j a b k = e8PairCoefficientDenominator k *
        (Int.toNat (-e8PairCoefficientNumerator i j a b k /
          e8PairCoefficientDenominator k) : ℤ)) := by
  decide +revert

private lemma e8PairVector_apply_eq_coordinate
    (i j : Fin 8) (a b : Bool) (k : Fin 8) :
    (((e8BoolSign a : ℝ) • basisVector i +
        (e8BoolSign b : ℝ) • basisVector j : Vec 8) k) =
      (e8PairCoordinate i j a b k : ℝ) := by
  cases a <;> cases b <;>
    by_cases hik : i = k <;> by_cases hjk : j = k <;>
      simp [e8BoolSign, e8PairCoordinate, basisVector, Pi.single_apply,
        hik, hjk, eq_comm] <;>
      norm_num

private lemma typeE8SimpleCoefficient_pair_scaled
    (i j : Fin 8) (a b : Bool) (k : Fin 8) :
    (e8PairCoefficientDenominator k : ℝ) *
        typeE8SimpleCoefficient
          ((e8BoolSign a : ℝ) • basisVector i + (e8BoolSign b : ℝ) • basisVector j) k =
      (e8PairCoefficientNumerator i j a b k : ℝ) := by
  fin_cases k <;>
    simp only [e8PairCoefficientDenominator, e8PairCoefficientNumerator,
      typeE8SimpleCoefficient, e8PairVector_apply_eq_coordinate] <;>
    push_cast <;>
    ring

private lemma typeE8SimpleCoefficient_pair_eq_nat
    (i j : Fin 8) (a b : Bool) (k : Fin 8) (n : ℕ)
    (h : e8PairCoefficientNumerator i j a b k =
      e8PairCoefficientDenominator k * (n : ℤ)) :
    typeE8SimpleCoefficient
        ((e8BoolSign a : ℝ) • basisVector i + (e8BoolSign b : ℝ) • basisVector j) k = n := by
  have hs := typeE8SimpleCoefficient_pair_scaled i j a b k
  have hR := congrArg (fun z : ℤ => (z : ℝ)) h
  fin_cases k <;>
    norm_num [e8PairCoefficientDenominator] at hs hR ⊢ <;>
    linarith

private lemma typeE8SimpleCoefficient_neg_pair_eq_nat
    (i j : Fin 8) (a b : Bool) (k : Fin 8) (n : ℕ)
    (h : -e8PairCoefficientNumerator i j a b k =
      e8PairCoefficientDenominator k * (n : ℤ)) :
    typeE8SimpleCoefficient
        (-((e8BoolSign a : ℝ) • basisVector i +
          (e8BoolSign b : ℝ) • basisVector j)) k = n := by
  rw [typeE8SimpleCoefficient_neg]
  have hs := typeE8SimpleCoefficient_pair_scaled i j a b k
  have hR := congrArg (fun z : ℤ => (z : ℝ)) h
  fin_cases k <;>
    norm_num [e8PairCoefficientDenominator] at hs hR ⊢ <;>
    linarith

private lemma e8PairVector_simpleCoefficients_nat_or_neg
    (i j : Fin 8) (a b : Bool) (hij : i ≠ j) :
    (∀ k, ∃ n : ℕ, typeE8SimpleCoefficient
        ((e8BoolSign a : ℝ) • basisVector i + (e8BoolSign b : ℝ) • basisVector j) k = n) ∨
      (∀ k, ∃ n : ℕ, typeE8SimpleCoefficient
        (-((e8BoolSign a : ℝ) • basisVector i +
          (e8BoolSign b : ℝ) • basisVector j)) k = n) := by
  rcases e8PairCoefficient_nat_or_neg i j a b hij with hpos | hneg
  · left
    intro k
    let n := Int.toNat
      (e8PairCoefficientNumerator i j a b k / e8PairCoefficientDenominator k)
    exact ⟨n, typeE8SimpleCoefficient_pair_eq_nat i j a b k n (hpos k)⟩
  · right
    intro k
    let n := Int.toNat
      (-e8PairCoefficientNumerator i j a b k / e8PairCoefficientDenominator k)
    exact ⟨n, typeE8SimpleCoefficient_neg_pair_eq_nat i j a b k n (hneg k)⟩

public lemma typeE8Root_simpleCoefficients_nat_or_neg (r : typeE8Roots) :
    (∀ i, ∃ n : ℕ, typeE8SimpleCoefficient r.1 i = n) ∨
      (∀ i, ∃ n : ℕ, typeE8SimpleCoefficient (-r.1) i = n) := by
  classical
  rcases r.2 with hrPair | ⟨ε, hε, hr⟩
  · rcases hrPair with ⟨i, j, hij, a, b, ha, hb, hr⟩
    rw [hr]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · simpa [e8BoolSign] using e8PairVector_simpleCoefficients_nat_or_neg i j false false hij
    · simpa [e8BoolSign] using e8PairVector_simpleCoefficients_nat_or_neg i j false true hij
    · simpa [e8BoolSign] using e8PairVector_simpleCoefficients_nat_or_neg i j true false hij
    · simpa [e8BoolSign] using e8PairVector_simpleCoefficients_nat_or_neg i j true true hij
  · rw [hr]
    rcases e8HalfCoefficient_nat_or_neg ε hε with hpos | hneg
    · left
      intro i
      let n := Int.toNat
        (e8HalfCoefficientNumerator ε i / e8HalfCoefficientDenominator i)
      exact ⟨n, typeE8SimpleCoefficient_halfSignVector_eq_nat ε i n (hpos i)⟩
    · right
      intro i
      let n := Int.toNat
        (-e8HalfCoefficientNumerator ε i / e8HalfCoefficientDenominator i)
      exact ⟨n, typeE8SimpleCoefficient_neg_halfSignVector_eq_nat ε i n (hneg i)⟩

@[expose] public noncomputable def typeE8SimpleClosure : AddSubmonoid (Vec 8) :=
  AddSubmonoid.closure (typeE8RootPairing.root '' Set.range typeE8SimpleRootIndex)

public lemma typeE8SimpleRoot_mem_simpleClosure (i : Fin 8) :
    typeE8RootPairing.root (typeE8SimpleRootIndex i) ∈ typeE8SimpleClosure := by
  apply AddSubmonoid.subset_closure
  exact ⟨_, ⟨i, rfl⟩, rfl⟩

public lemma typeE8RootPairing_root_mem_or_neg_mem_simpleClosure (r : typeE8Roots) :
    typeE8RootPairing.root r ∈
        AddSubmonoid.closure (typeE8RootPairing.root '' Set.range typeE8SimpleRootIndex) ∨
      -typeE8RootPairing.root r ∈
        AddSubmonoid.closure (typeE8RootPairing.root '' Set.range typeE8SimpleRootIndex) := by
  change typeE8RootPairing.root r ∈ typeE8SimpleClosure ∨
    -typeE8RootPairing.root r ∈ typeE8SimpleClosure
  rcases typeE8Root_simpleCoefficients_nat_or_neg r with hpos | hneg
  · left
    choose n hn using hpos
    have hmem : ∑ i, n i • typeE8RootPairing.root (typeE8SimpleRootIndex i) ∈
        typeE8SimpleClosure :=
      AddSubmonoid.sum_mem _ fun i _ =>
        AddSubmonoid.nsmul_mem typeE8SimpleClosure (typeE8SimpleRoot_mem_simpleClosure i) (n i)
    convert hmem using 1
    simp only [typeE8RootPairing_root, typeE8SimpleRootIndex_val]
    rw [← typeE8SimpleCoefficient_reconstruction r.1]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← hn i]
  · right
    choose n hn using hneg
    have hmem : ∑ i, n i • typeE8RootPairing.root (typeE8SimpleRootIndex i) ∈
        typeE8SimpleClosure :=
      AddSubmonoid.sum_mem _ fun i _ =>
        AddSubmonoid.nsmul_mem typeE8SimpleClosure (typeE8SimpleRoot_mem_simpleClosure i) (n i)
    convert hmem using 1
    simp only [typeE8RootPairing_root, typeE8SimpleRootIndex_val]
    rw [← typeE8SimpleCoefficient_reconstruction (-r.1)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← hn i]

/-- The displayed type `E₈` base in the coordinate order fixed by `Exceptional`. -/
@[expose] public noncomputable def typeE8RootPairing_base : typeE8RootPairing.Base :=
  RootPairing.Base.mk' typeE8RootPairing (Set.range typeE8SimpleRootIndex)
    typeE8RootPairing_linearIndepOn_simpleRoots
    typeE8RootPairing_root_mem_or_neg_mem_simpleClosure

public lemma typeE8RootPairing_base_support :
    (typeE8RootPairing_base.support : Set typeE8Roots) =
      Set.range typeE8SimpleRootIndex := by
  simp [typeE8RootPairing_base, RootPairing.Base.mk']

/-- The standard numbering of the displayed E8 base by `Fin 8`. -/
@[expose] public noncomputable def typeE8RootPairing_baseEquiv :
    Fin 8 ≃ typeE8RootPairing_base.support :=
  (Equiv.ofInjective typeE8SimpleRootIndex typeE8SimpleRootIndex_injective).trans
    (Equiv.setCongr typeE8RootPairing_base_support.symm)

@[simp] public lemma typeE8RootPairing_baseEquiv_val (i : Fin 8) :
    (typeE8RootPairing_baseEquiv i : typeE8Roots) = typeE8SimpleRootIndex i := rfl

public lemma typeE8RootPairing_base_cartan_apply (i j : Fin 8) :
    typeE8RootPairing_base.cartanMatrix
        (typeE8RootPairing_baseEquiv i) (typeE8RootPairing_baseEquiv j) =
      typeE8CartanMatrix i j := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  rw [typeE8RootPairing_baseEquiv_val, typeE8RootPairing_baseEquiv_val]
  exact typeE8RootPairing_simpleIndex_pairing i j

/-- The displayed base has exactly the standard type `E₈` Cartan matrix. -/
public theorem typeE8RootPairing_base_cartan :
    typeE8RootPairing_base.cartanMatrix.reindex
        typeE8RootPairing_baseEquiv.symm typeE8RootPairing_baseEquiv.symm =
      typeE8CartanMatrix := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact typeE8RootPairing_base_cartan_apply i j

public lemma typeE8Cartan_connected (i j : Fin 8) :
    Relation.ReflTransGen (fun u v : Fin 8 => typeE8CartanMatrix u v ≠ 0) i j := by
  let edge := fun u v : Fin 8 => typeE8CartanMatrix u v ≠ 0
  have h01 : edge 0 1 := by decide
  have h10 : edge 1 0 := by decide
  have h12 : edge 1 2 := by decide
  have h21 : edge 2 1 := by decide
  have h23 : edge 2 3 := by decide
  have h32 : edge 3 2 := by decide
  have h24 : edge 2 4 := by decide
  have h42 : edge 4 2 := by decide
  have h45 : edge 4 5 := by decide
  have h54 : edge 5 4 := by decide
  have h56 : edge 5 6 := by decide
  have h65 : edge 6 5 := by decide
  have h67 : edge 6 7 := by decide
  have h76 : edge 7 6 := by decide
  have hto : ∀ k : Fin 8, Relation.ReflTransGen edge k 0 := by
    intro k
    fin_cases k
    · exact .refl
    · exact .single h10
    · exact (Relation.ReflTransGen.single h21).tail h10
    · exact ((Relation.ReflTransGen.single h32).tail h21).tail h10
    · exact ((Relation.ReflTransGen.single h42).tail h21).tail h10
    · exact (((Relation.ReflTransGen.single h54).tail h42).tail h21).tail h10
    · exact ((((Relation.ReflTransGen.single h65).tail h54).tail h42).tail h21).tail h10
    · exact (((((Relation.ReflTransGen.single h76).tail h65).tail h54).tail h42).tail h21).tail h10
  have hfrom : ∀ k : Fin 8, Relation.ReflTransGen edge 0 k := by
    intro k
    fin_cases k
    · exact .refl
    · exact .single h01
    · exact (Relation.ReflTransGen.single h01).tail h12
    · exact ((Relation.ReflTransGen.single h01).tail h12).tail h23
    · exact ((Relation.ReflTransGen.single h01).tail h12).tail h24
    · exact (((Relation.ReflTransGen.single h01).tail h12).tail h24).tail h45
    · exact ((((Relation.ReflTransGen.single h01).tail h12).tail h24).tail h45).tail h56
    · exact (((((Relation.ReflTransGen.single h01).tail h12).tail h24).tail h45).tail h56).tail h67
  exact (hto i).trans (hfrom j)

public lemma typeE8RootPairing_base_cartan_connected
    (s t : typeE8RootPairing_base.support) :
    Relation.ReflTransGen
      (fun u v : typeE8RootPairing_base.support =>
        typeE8RootPairing_base.cartanMatrix u v ≠ 0) s t := by
  rw [← typeE8RootPairing_baseEquiv.apply_symm_apply s,
    ← typeE8RootPairing_baseEquiv.apply_symm_apply t]
  exact Relation.ReflTransGen.lift typeE8RootPairing_baseEquiv
    (fun i j h => by
      change typeE8RootPairing_base.cartanMatrix
        (typeE8RootPairing_baseEquiv i) (typeE8RootPairing_baseEquiv j) ≠ 0
      rw [typeE8RootPairing_base_cartan_apply]
      exact h)
    _ _ (typeE8Cartan_connected _ _)

public instance typeE8RootPairing_isIrreducible : typeE8RootPairing.IsIrreducible :=
  isIrreducible_of_cartan_connected typeE8RootPairing typeE8RootPairing_base
    ⟨(typeE8RootPairing_baseEquiv 0 : typeE8Roots),
      (typeE8RootPairing_baseEquiv 0).property⟩
    typeE8RootPairing_base_cartan_connected

/-- Existence of the standard finite, reduced, crystallographic, irreducible
type `E₈` root pairing, with its numbered Cartan matrix. -/
public theorem typeE8_standardRootPairing_exists :
    typeE8RootPairing.IsRootSystem ∧ typeE8RootPairing.IsCrystallographic ∧
      typeE8RootPairing.IsReduced ∧ typeE8RootPairing.IsIrreducible ∧
        ∃ (b : typeE8RootPairing.Base) (numbering : Fin 8 ≃ b.support),
          b.cartanMatrix.reindex numbering.symm numbering.symm = typeE8CartanMatrix := by
  refine ⟨typeE8RootPairing_isRootSystem, typeE8RootPairing_isCrystallographic,
    typeE8RootPairing_isReduced, typeE8RootPairing_isIrreducible,
    typeE8RootPairing_base, typeE8RootPairing_baseEquiv, ?_⟩
  exact typeE8RootPairing_base_cartan

end Theory.AlgebraicGroup.StandardRootSystem
