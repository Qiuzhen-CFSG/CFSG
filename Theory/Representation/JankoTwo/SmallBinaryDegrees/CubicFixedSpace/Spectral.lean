module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace.RankDivisibility
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace.PowerConjugacy
public import Theory.Representation.ScalarDescent
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic

/-!
# Displacement ranks under squaring conjugacy

An element of exponent three or seven that is conjugate to its square has
characteristic-two displacement rank divisible by two or three, respectively.
No faithfulness, irreducibility, degree bound or finite-field hypothesis is used.

Extend scalars to an algebraic closure. Separability of X^p - 1 decomposes the
space into eigenspaces indexed by powers of a primitive p-th root. The inverse
conjugator embeds each eigenspace into the one with squared eigenvalue. Around
each finite cycle their dimensions are equal: the nonidentity cycles have
length two for p = 3 and length three for p = 7. Rank-nullity removes the
identity eigenspace. Kernel base change and rank-nullity descend the rank to
the original field.

The applications use the checked power identities and conjugators for the
literal J₂ generators b and ab. These discharge the two rank premises in
`SmallBinaryDegrees.cubicFixedSpaceCalculations_of_powerConjugacyRanks`.
Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript p.16, J₂ paragraph; permutation provenance is recorded in
`CubicFixedSpace/source/README.md`.
-/

public section

open Polynomial Module
open scoped DirectSum TensorProduct
namespace Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace
namespace Spectral
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem eigenvalue_pow_eq_one (f : Module.End K V) {p : ℕ} (hf : f ^ p = 1)
    {μ : K} (hμ : f.HasEigenvalue μ) : μ ^ p = 1 := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hh := hv.pow_apply p
  rw [hf, Module.End.one_apply] at hh
  exact (smul_left_injective K hv.2) (hh.symm.trans (one_smul K v).symm)

private theorem dimension_eq_sum [FiniteDimensional K V] [IsAlgClosed K]
    (f : Module.End K V) {p : ℕ} [NeZero p] (hp : (p : K) ≠ 0)
    (hf : f ^ p = 1) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    finrank K V = ∑ i : Fin p, finrank K (f.eigenspace (ζ ^ i.val)) := by
  classical
  have hs : f.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := (X : K[X]) ^ p - 1)
    · exact (X_pow_sub_one_separable_iff.mpr hp).squarefree
    · simp [hf]
  have hspan : (⨆ i : Fin p, f.eigenspace (ζ ^ i.val)) = ⊤ := by
    apply top_unique
    rw [← hs.iSup_eigenspace_eq_top]
    refine iSup_le fun μ => ?_
    by_cases hμ : f.eigenspace μ = ⊥
    · simp [hμ]
    · obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one (eigenvalue_pow_eq_one f hf hμ)
      exact le_iSup (fun i : Fin p => f.eigenspace (ζ ^ i.val)) ⟨i, hi⟩
  have hind : iSupIndep (fun i : Fin p => f.eigenspace (ζ ^ i.val)) :=
    f.eigenspaces_iSupIndep.comp (fun i j h => Fin.ext (hζ.pow_inj i.isLt j.isLt h))
  let e := LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun i : Fin p => f.eigenspace (ζ ^ i.val)))
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hspan)
  rw [← e.finrank_eq, Module.finrank_directSum]

private theorem eigenspace_square_le [Group G] [FiniteDimensional K V]
    (ρ : Representation K G V) (x g : G) (hg : g * x * g⁻¹ = x ^ 2) (μ : K) :
    finrank K (Module.End.eigenspace (ρ x) μ) ≤ finrank K (Module.End.eigenspace (ρ x) (μ ^ 2)) := by
  have hc : x * g⁻¹ = g⁻¹ * x ^ 2 := by rw [← hg]; group
  have hmap (v : Module.End.eigenspace (ρ x) μ) :
      ρ g⁻¹ (v : V) ∈ Module.End.eigenspace (ρ x) (μ ^ 2) := by
    rw [Module.End.mem_eigenspace_iff]
    have hv := Module.End.mem_eigenspace_iff.mp v.property
    calc
      ρ x (ρ g⁻¹ v) = ρ g⁻¹ ((ρ x ^ 2) v) := by
        rw [← map_pow]
        change (ρ x * ρ g⁻¹) _ = (ρ g⁻¹ * ρ (x ^ 2)) _
        rw [← map_mul, ← map_mul, hc]
      _ = μ ^ 2 • ρ g⁻¹ v := by
        simp [pow_two, Module.End.mul_apply, hv, smul_smul]
  let j := ((ρ g⁻¹).comp (Module.End.eigenspace (ρ x) μ).subtype).codRestrict _ hmap
  apply LinearMap.finrank_le_finrank_of_injective (f := j)
  intro v w hvw
  apply Subtype.ext
  have hh := congrArg (fun z : Module.End.eigenspace (ρ x) (μ ^ 2) => ρ g (z : V)) hvw
  change ρ g (ρ g⁻¹ (v : V)) = ρ g (ρ g⁻¹ (w : V)) at hh
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using hh

private theorem kernel_eq_eigenspace (f : Module.End K V) :
    (f - 1).ker = f.eigenspace 1 := by
  ext v
  simp [LinearMap.mem_ker, sub_eq_zero]

private theorem cubic_rank [Group G] [FiniteDimensional K V] [IsAlgClosed K]
    (ρ : Representation K G V) (x g : G) (hx : x ^ 3 = 1)
    (hg : g * x * g⁻¹ = x ^ 2) (h3 : (3 : K) ≠ 0) :
    2 ∣ finrank K (LinearMap.range (ρ x - 1)) := by
  let : NeZero (3 : K) := ⟨h3⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K 3
  have hdim := dimension_eq_sum (ρ x) h3 (by rw [← map_pow, hx, map_one]) hζ
  have h12 := eigenspace_square_le ρ x g hg ζ
  have h21 := eigenspace_square_le ρ x g hg (ζ ^ 2)
  have h4 : (ζ ^ 2) ^ 2 = ζ := by
    rw [← pow_mul]
    change ζ ^ (3 + 1) = ζ
    rw [pow_add, hζ.pow_eq_one, one_mul, pow_one]
  rw [h4] at h21
  let m : K → ℕ := fun μ => finrank K (Module.End.eigenspace (ρ x) μ)
  change finrank K V = ∑ i : Fin 3, m (ζ ^ i.val) at hdim
  norm_num [Fin.sum_univ_succ] at hdim
  have hr := (ρ x - 1).finrank_range_add_finrank_ker
  rw [kernel_eq_eigenspace] at hr
  change m ζ ≤ m (ζ ^ 2) at h12
  change m (ζ ^ 2) ≤ m ζ at h21
  change finrank K (LinearMap.range (ρ x - 1)) + m 1 = finrank K V at hr
  exact ⟨m ζ, by omega⟩

private theorem septic_rank [Group G] [FiniteDimensional K V] [IsAlgClosed K]
    (ρ : Representation K G V) (x g : G) (hx : x ^ 7 = 1)
    (hg : g * x * g⁻¹ = x ^ 2) (h7 : (7 : K) ≠ 0) :
    3 ∣ finrank K (LinearMap.range (ρ x - 1)) := by
  let : NeZero (7 : K) := ⟨h7⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K 7
  have hdim := dimension_eq_sum (ρ x) h7 (by rw [← map_pow, hx, map_one]) hζ
  have h12 := eigenspace_square_le ρ x g hg ζ
  have h24 := eigenspace_square_le ρ x g hg (ζ ^ 2)
  have h41 := eigenspace_square_le ρ x g hg (ζ ^ 4)
  have h36 := eigenspace_square_le ρ x g hg (ζ ^ 3)
  have h65 := eigenspace_square_le ρ x g hg (ζ ^ 6)
  have h53 := eigenspace_square_le ρ x g hg (ζ ^ 5)
  have hp (n : ℕ) : ζ ^ (7 + n) = ζ ^ n := by rw [pow_add, hζ.pow_eq_one, one_mul]
  rw [← pow_mul] at h24 h36
  rw [← pow_mul, show 4 * 2 = 7 + 1 from rfl, hp, pow_one] at h41
  rw [← pow_mul, show 6 * 2 = 7 + 5 from rfl, hp] at h65
  rw [← pow_mul, show 5 * 2 = 7 + 3 from rfl, hp] at h53
  let m : K → ℕ := fun μ => finrank K (Module.End.eigenspace (ρ x) μ)
  change finrank K V = ∑ i : Fin 7, m (ζ ^ i.val) at hdim
  norm_num [Fin.sum_univ_succ] at hdim
  have hr := (ρ x - 1).finrank_range_add_finrank_ker
  rw [kernel_eq_eigenspace] at hr
  change m ζ ≤ m (ζ ^ 2) at h12
  change m (ζ ^ 2) ≤ m (ζ ^ 4) at h24
  change m (ζ ^ 4) ≤ m ζ at h41
  change m (ζ ^ 3) ≤ m (ζ ^ 6) at h36
  change m (ζ ^ 6) ≤ m (ζ ^ 5) at h65
  change m (ζ ^ 5) ≤ m (ζ ^ 3) at h53
  change finrank K (LinearMap.range (ρ x - 1)) + m 1 = finrank K V at hr
  exact ⟨m ζ + m (ζ ^ 3), by omega⟩

private theorem displacement_rank_extendScalars [Group G] [FiniteDimensional K V]
    (ρ : Representation K G V) (x : G) (E : Type*) [Field E] [Algebra K E] :
    finrank E (LinearMap.range (extendScalars E ρ x - 1)) =
      finrank K (LinearMap.range (ρ x - 1)) := by
  have hk := (LinearMap.kerBaseChangeEquiv (E := E) (ρ x - 1)).finrank_eq
  rw [Module.finrank_baseChange, LinearMap.baseChange_sub, LinearMap.baseChange_one] at hk
  have hE := (extendScalars E ρ x - 1).finrank_range_add_finrank_ker
  have hK := (ρ x - 1).finrank_range_add_finrank_ker
  rw [Module.finrank_baseChange] at hE
  change finrank K (ρ x - 1).ker = finrank E (extendScalars E ρ x - 1).ker at hk
  omega

end Spectral
universe u v

/-- An element of exponent three conjugate to its square has even displacement
rank over every characteristic-two field. -/
theorem powerConjugacyRankDivisibility_three : PowerConjugacyRankDivisibility.{u,v} 3 2 := by
  intro K _ _ V _ _ _ G _ ρ x hx hconj
  obtain ⟨g, hg⟩ := hconj
  let E := AlgebraicClosure K
  have h3 : (3 : E) ≠ 0 := (CharP.cast_eq_zero_iff E 2 3).not.mpr (by decide)
  have h := Spectral.cubic_rank (extendScalars E ρ) x g hx hg h3
  rwa [Spectral.displacement_rank_extendScalars] at h

/-- An element of exponent seven conjugate to its square has displacement
rank divisible by three over every characteristic-two field. -/
theorem powerConjugacyRankDivisibility_seven : PowerConjugacyRankDivisibility.{u,v} 7 3 := by
  intro K _ _ V _ _ _ G _ ρ x hx hconj
  obtain ⟨g, hg⟩ := hconj
  let E := AlgebraicClosure K
  have h7 : (7 : E) ≠ 0 := (CharP.cast_eq_zero_iff E 2 7).not.mpr (by decide)
  have h := Spectral.septic_rank (extendScalars E ρ) x g hx hg h7
  rwa [Spectral.displacement_rank_extendScalars] at h

open Sporadic.LeechRelated.J2

/-- The checked cubic conjugator supplies even displacement for the literal
J₂ generator `b`, discharging the cubic rank premise in Scott's reduction. -/
theorem two_dvd_cubic_displacement_rank
    {K V : Type v} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Representation K Carrier V) :
    2 ∣ finrank K (LinearMap.range (ρ GeneratorPair.b - 1)) :=
  powerConjugacyRankDivisibility_three K V Carrier ρ GeneratorPair.b
    GeneratorPair.b_pow_three exists_conjugator_cubic_square

/-- The checked septic conjugator supplies displacement divisible by three
for the literal J₂ element `ab`, discharging Scott's septic rank premise. -/
theorem three_dvd_septic_displacement_rank
    {K V : Type v} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Representation K Carrier V) :
    3 ∣ finrank K (LinearMap.range (ρ (GeneratorPair.a * GeneratorPair.b) - 1)) :=
  powerConjugacyRankDivisibility_seven K V Carrier ρ (GeneratorPair.a * GeneratorPair.b)
    GeneratorPair.ab_pow_seven exists_conjugator_septic_square

end Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace
