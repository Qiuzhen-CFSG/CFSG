module

public import Theory.RingTheory.MonoidAlgebraInvariantGeneration
/-!
# Fundamental orbit sums generate and separate

Products of the fundamental orbit sums supply the monic highest-term
replacements from a genuine dominant-weight factorization. Triangular
subtraction then generates the full invariant algebra. Evaluation on this
algebra and finite-orbit separation show that the fundamental sums already
separate torus orbits.

The height, dominance and factorization hypotheses are lattice statements,
not assumptions about conjugacy classes. The actual F4 lattice application
must discharge them before invoking the Ree class count.
Source: Steinberg (1963), §3.9(b).
-/

open scoped BigOperators
open Classical
open Theory.MonoidAlgebraOrbitSums Theory.MonoidAlgebraHighestTerm
open Theory.MonoidAlgebraInvariantGeneration
public noncomputable section
namespace Theory.FundamentalOrbitSums
variable {F G L I : Type*} [Field F] [Group G] [Finite G] [CommGroup L]
  [MulDistribMulAction G L] [Fintype I]

@[expose] noncomputable def gamma (a : L) : MonoidAlgebra F L :=
  Theory.PermutationBasisOrbitSums.orbitSum (G := G) (MonoidAlgebra.basis L F) a

lemma gamma_coeff (a b : L) : (gamma (F := F) (G := G) a).coeff b =
    if b ∈ MulAction.orbit G a then 1 else 0 := by
  classical
  exact Theory.PermutationBasisOrbitSums.coeff_orbitSum (MonoidAlgebra.basis L F) a b

lemma gamma_invariant (a : L) : Invariant (G := G) (gamma (F := F) (G := G) a) :=
  fun g => algebraAction_orbitSum g a

lemma gamma_leading (d : L → ℤ) (a : L)
    (hle : ∀ g : G, d (g • a) ≤ d a)
    (heq : ∀ g : G, d (g • a) = d a → g • a = a) :
    LeadingAt d (gamma (F := F) (G := G) a) a := by
  classical
  have hmem : ∀ b, b ∈ (gamma (F := F) (G := G) a).coeff.support →
      b ∈ MulAction.orbit G a := by
    intro b hb
    rw [Finsupp.mem_support_iff, gamma_coeff] at hb
    by_contra h
    exact hb (if_neg h)
  refine ⟨?_, ?_, ?_⟩
  · simp only [gamma_coeff, MulAction.mem_orbit_self, ↓reduceIte]
  · intro b hb
    obtain ⟨g, rfl⟩ := hmem b hb
    exact hle g
  · intro b hb hba
    obtain ⟨g, rfl⟩ := hmem b hb
    exact heq g hba

/-- The highest-term products associated to actual dominant factorizations
place every invariant polynomial in the fundamental orbit-sum algebra. -/
theorem invariant_mem_adjoin_fundamental
    (d : L → ℤ) (hd : ∀ a b, d (a * b) = d a + d b) (ω : I → L)
    (hpos : ∀ a : L, (∀ g : G, d (g • a) ≤ d a) → 0 ≤ d a)
    (hfactor : ∀ a : L, (∀ g : G, d (g • a) ≤ d a) →
      ∃ n : I → ℕ, a = ∏ i, ω i ^ n i)
    (hle : ∀ (i : I) (g : G), d (g • ω i) ≤ d (ω i))
    (heq : ∀ (i : I) (g : G), d (g • ω i) = d (ω i) → g • ω i = ω i)
    (p : MonoidAlgebra F L) (hp : Invariant (G := G) p) :
    p ∈ Algebra.adjoin F (Set.range (fun i => gamma (F := F) (G := G) (ω i))) := by
  classical
  apply invariant_mem_of_highest_replacements (G := G) d _ hpos _ p hp
  intro a ha
  obtain ⟨n, rfl⟩ := hfactor a ha
  let q := ∏ i, gamma (F := F) (G := G) (ω i) ^ n i
  refine ⟨q, ?_, ?_, ?_⟩
  · apply Subalgebra.prod_mem
    intro i _
    apply pow_mem
    exact Algebra.subset_adjoin (Set.mem_range_self i)
  · intro g
    simp only [q, map_prod, map_pow, algebraAction_orbitSum, gamma]
  · exact LeadingAt.finset_prod hd Finset.univ
      (fun i => gamma (F := F) (G := G) (ω i) ^ n i) (fun i => ω i ^ n i)
      (fun i _ => (gamma_leading d (ω i) (hle i) (heq i)).pow hd (n i))

/-- Equality of fundamental orbit sums suffices once the genuine lattice
highest-weight and dominant-factorization facts have been established. -/
theorem exists_smul_of_fundamental_values_eq
    (d : L → ℤ) (hd : ∀ a b, d (a * b) = d a + d b) (ω : I → L)
    (hpos : ∀ a : L, (∀ g : G, d (g • a) ≤ d a) → 0 ≤ d a)
    (hfactor : ∀ a : L, (∀ g : G, d (g • a) ≤ d a) →
      ∃ n : I → ℕ, a = ∏ i, ω i ^ n i)
    (hle : ∀ (i : I) (g : G), d (g • ω i) ≤ d (ω i))
    (heq : ∀ (i : I) (g : G), d (g • ω i) = d (ω i) → g • ω i = ω i)
    (t s : L →* Fˣ)
    (hvalues : ∀ i : I, orbitSumValue (G := G) t (ω i) =
      orbitSumValue (G := G) s (ω i)) :
    ∃ g : G, ∀ a : L, s a = t (g • a) := by
  have hsame : Set.EqOn (pointEvaluation t) (pointEvaluation s)
      (Set.range (fun i => gamma (F := F) (G := G) (ω i))) := by
    rintro _ ⟨i, rfl⟩
    exact hvalues i
  have hgen := AlgHom.adjoin_le_equalizer (pointEvaluation t) (pointEvaluation s) hsame
  apply exists_smul_of_orbitSumValue_eq
  intro a
  exact hgen (invariant_mem_adjoin_fundamental d hd ω hpos hfactor hle heq
    (gamma (F := F) (G := G) a) (gamma_invariant a))
end Theory.FundamentalOrbitSums
