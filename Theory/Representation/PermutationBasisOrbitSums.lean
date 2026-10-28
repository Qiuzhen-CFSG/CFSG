module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# Invariants of a permutation basis

An invariant finite linear combination has constant coefficients on each
basis orbit. Removing one complete orbit decreases its support, so the
invariant vectors are spanned by sums of distinct orbit elements. The
argument works when the group order is zero in the coefficient field;
there is no averaging operator or stabilizer multiplicity.

Source: Steinberg (1963), §3.9, invariant Laurent-polynomial argument.
-/

open scoped BigOperators
open Module
open Classical

public noncomputable section
namespace Theory.PermutationBasisOrbitSums
variable {F A G I : Type*} [Field F] [AddCommGroup A] [Module F A]
  [Group G] [Finite G] [MulAction G I]
@[expose] noncomputable def orbitSum (b : Basis I F A) (i : I) : A :=
  ∑ j ∈ (Set.finite_range (fun g : G => g • i)).toFinset, b j

lemma coeff_orbitSum (b : Basis I F A) (i j : I) :
    b.repr (orbitSum (G := G) b i) j = if j ∈ MulAction.orbit G i then 1 else 0 := by
  classical
  simp [orbitSum, map_sum, Finsupp.finsetSum_apply, b.repr_self, Finsupp.single_apply,
    eq_comm, MulAction.orbit]

omit [Finite G] in
lemma orbit_mem_smul_iff (i j : I) (g : G) :
    g • j ∈ MulAction.orbit G i ↔ j ∈ MulAction.orbit G i := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨g⁻¹ * a, by simp only [mul_smul, ha, inv_smul_smul]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨g * a, mul_smul _ _ _⟩

/-- Coefficient-constant finite sums are linear combinations of orbit sums. -/
theorem mem_span_orbitSum (b : Basis I F A) (p : A)
    (hp : ∀ (g : G) (i : I), b.repr p (g • i) = b.repr p i) :
    p ∈ Submodule.span F (Set.range (orbitSum (G := G) b)) := by
  classical
  generalize hn : (b.repr p).support.card = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hzero : p = 0
    · simp [hzero]
    have hne : (b.repr p).support.Nonempty := by
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp (show b.repr p ≠ 0 from
        fun h => hzero (b.repr.injective (by simpa using h)))
      exact ⟨i, Finsupp.mem_support_iff.mpr (by simpa using hi)⟩
    obtain ⟨i, hi⟩ := hne
    let c := b.repr p i
    let q := p - c • orbitSum (G := G) b i
    have hc : c ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hcoeff (j : I) : b.repr q j =
        if j ∈ MulAction.orbit G i then 0 else b.repr p j := by
      have he : j ∈ MulAction.orbit G i → b.repr p j = c := by
        rintro ⟨g, rfl⟩
        exact hp g i
      simp only [q, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
        smul_eq_mul, coeff_orbitSum]
      split_ifs with hj
      · rw [he hj, mul_one, sub_self]
      · simp
    have hq : ∀ (g : G) (j : I), b.repr q (g • j) = b.repr q j := by
      intro g j
      simp only [hcoeff, orbit_mem_smul_iff, hp]
    have hsub : (b.repr q).support ⊂ (b.repr p).support := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro j hj
        rw [Finsupp.mem_support_iff, hcoeff] at hj
        rw [Finsupp.mem_support_iff]
        split_ifs at hj with hj'
        · exact False.elim (hj rfl)
        · exact hj
      · intro he
        have hiq : i ∈ (b.repr q).support := he.symm ▸ hi
        rw [Finsupp.mem_support_iff, hcoeff] at hiq
        exact hiq (by simp only [MulAction.mem_orbit_self, ↓reduceIte])
    have hlt : (b.repr q).support.card < n := by
      rw [← hn]
      exact Finset.card_lt_card hsub
    have hqm := ih _ hlt q hq rfl
    have hiM : orbitSum (G := G) b i ∈
        Submodule.span F (Set.range (orbitSum (G := G) b)) :=
      Submodule.subset_span (Set.mem_range_self _)
    have he : p = q + c • orbitSum (G := G) b i := by simp only [q, sub_add_cancel]
    rw [he]
    exact Submodule.add_mem _ hqm (Submodule.smul_mem _ c hiM)

variable [DistribMulAction G A] [SMulCommClass G F A]

omit [Finite G] in
lemma repr_smul (b : Basis I F A)
    (hb : ∀ (g : G) (i : I), g • b i = b (g • i))
    (g : G) (p : A) (i : I) : b.repr (g • p) (g • i) = b.repr p i := by
  let f : A →ₗ[F] F := (Finsupp.lapply (g • i)).comp
    (b.repr.toLinearMap.comp (DistribSMul.toLinearMap F A g))
  let h : A →ₗ[F] F := (Finsupp.lapply i).comp b.repr.toLinearMap
  have he : f = h := by
    apply b.ext
    intro j
    change b.repr (g • b j) (g • i) = b.repr (b j) i
    rw [hb]
    simp [b.repr_self, Finsupp.single_apply]
  exact LinearMap.congr_fun he p

/-- A distinct-orbit sum is fixed by the permutation action. -/
lemma smul_orbitSum (b : Basis I F A)
    (hb : ∀ (g : G) (i : I), g • b i = b (g • i))
    (g : G) (i : I) : g • orbitSum (G := G) b i = orbitSum (G := G) b i := by
  apply b.repr.injective
  ext j
  have h := repr_smul b hb g (orbitSum (G := G) b i) (g⁻¹ • j)
  simp only [smul_inv_smul] at h
  rw [h, coeff_orbitSum, coeff_orbitSum, orbit_mem_smul_iff]

lemma invariant_mem_span_orbitSum (b : Basis I F A)
    (hb : ∀ (g : G) (i : I), g • b i = b (g • i))
    (p : A) (hp : ∀ g : G, g • p = p) :
    p ∈ Submodule.span F (Set.range (orbitSum (G := G) b)) := by
  apply mem_span_orbitSum b p
  intro g i
  rw [← hp g]
  rw [repr_smul b hb]
  rw [hp]
end Theory.PermutationBasisOrbitSums
