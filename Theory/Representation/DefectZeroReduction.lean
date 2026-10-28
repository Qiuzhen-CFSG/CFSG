module

public import Theory.Representation.CoefficientReduction
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Irreducibility after defect-zero coefficient reduction

Suppose an integral matrix representation has irreducible complex extension
of degree `n`, and the group order is `n * q`. If `q` stays nonzero in a
residue field, the coefficient reduction is irreducible.

Schur's lemma makes the sum of conjugates of each endomorphism scalar;
its trace determines that scalar. Applied to rank-one maps, this gives
matrix-coefficient orthogonality. An injective complex coefficient map
detects these identities over the original ring, and every residue map
preserves them. Thus `q` times every matrix unit is a linear combination
of the reduced action matrices. Every nonzero invariant subspace consequently
contains the entire coordinate basis. No invertibility of the group order
in the residue field, lattice existence, or modular block realization is used.

Source: the defect-zero reduction theorem, Feit, *The Representation Theory
of Finite Groups*, IV.4.19–20, printed pp.159–160. The proof here uses ordinary
Schur orthogonality directly, so the coefficient ring need only be commutative
with an injective map to the complex numbers.
-/

public section
noncomputable section
open scoped BigOperators

namespace Representation
namespace DefectZeroReduction

variable {G : Type*} [Group G] [Fintype G] {n q : ℕ}

private theorem conjugate_sum (ρ : Representation ℂ G (Fin n → ℂ)) [ρ.IsIrreducible]
    (hn : 0 < n) (horder : Nat.card G = n * q)
    (A : Module.End ℂ (Fin n → ℂ)) :
    (∑ g : G, ρ g * A * ρ g⁻¹) =
      ((q : ℂ) * LinearMap.trace ℂ _ A) • (1 : Module.End ℂ (Fin n → ℂ)) := by
  let τ := linHom ρ ρ
  let T := ∑ g : G, τ g A
  have hT : T ∈ τ.invariants := by
    intro h
    simp only [T, map_sum, ← Module.End.mul_apply, ← map_mul]
    exact Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun _ => rfl)
  let f : IntertwiningMap ρ ρ := invariantsEquivIntertwiningMap ρ ρ ⟨T, hT⟩
  obtain ⟨a, ha⟩ :=
    (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective f
  have hscalar : (∑ g : G, ρ g * A * ρ g⁻¹) = a • (1 : Module.End ℂ (Fin n → ℂ)) := by
    exact (congrArg IntertwiningMap.toLinearMap ha).symm
  have htrace := congrArg (LinearMap.trace ℂ (Fin n → ℂ)) hscalar
  have hconj (g : G) : LinearMap.trace ℂ _ (ρ g * A * ρ g⁻¹) =
      LinearMap.trace ℂ _ A := by
    rw [LinearMap.trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one, one_mul]
  simp only [map_sum, hconj, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, map_smul, smul_eq_mul, LinearMap.trace_one,
    Module.finrank_fin_fun, Fintype.card_eq_nat_card, horder, Nat.cast_mul] at htrace
  have ha' : a = (q : ℂ) * LinearMap.trace ℂ _ A := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    apply mul_right_cancel₀ hn'
    calc
      a * (n : ℂ) = ((n : ℂ) * q) * LinearMap.trace ℂ _ A := htrace.symm
      _ = ((q : ℂ) * LinearMap.trace ℂ _ A) * n := by ring
  rw [hscalar, ha']

private theorem coefficient_orthogonality (ρ : Representation ℂ G (Fin n → ℂ)) [ρ.IsIrreducible]
    (hn : 0 < n) (horder : Nat.card G = n * q) (a b i j : Fin n) :
    (∑ g : G, LinearMap.toMatrix' (ρ g⁻¹) j i * LinearMap.toMatrix' (ρ g) a b) =
      (q : ℂ) * (if a = i then 1 else 0) * (if b = j then 1 else 0) := by
  classical
  have h := congrArg (fun T : Module.End ℂ (Fin n → ℂ) => T (Pi.single i 1) a)
    (conjugate_sum ρ hn horder ((LinearMap.proj j).smulRight (Pi.single b 1)))
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    Module.End.one_apply, LinearMap.trace_smulRight, LinearMap.proj_apply,
    Module.End.mul_apply, LinearMap.smulRight_apply, map_smul, smul_eq_mul] at h
  by_cases hai : a = i <;> by_cases hbj : b = j <;>
    simpa [hai, hbj, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smulRight_apply,
      LinearMap.toMatrix'_apply, Pi.single_apply, mul_assoc, mul_comm, mul_left_comm,
      eq_comm, ite_apply, LinearMap.smul_apply, Pi.smul_apply, Module.End.one_apply] using h

private theorem matrix_unit_sum {k : Type*} [Field k]
    (ρ : Representation k G (Fin n → k))
    (horth : ∀ a b i j : Fin n,
      (∑ g : G, LinearMap.toMatrix' (ρ g⁻¹) j i * LinearMap.toMatrix' (ρ g) a b) =
        (q : k) * (if a = i then 1 else 0) * (if b = j then 1 else 0))
    (i j : Fin n) :
    (∑ g : G, LinearMap.toMatrix' (ρ g⁻¹) j i • ρ g) =
      (q : k) • (LinearMap.proj j).smulRight (Pi.single i 1) := by
  classical
  apply LinearMap.toMatrix'.injective
  ext a b
  simpa [LinearMap.toMatrix'_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
    Pi.single_apply, mul_assoc, mul_comm, mul_left_comm, eq_comm, ite_apply] using horth a b i j

private theorem reduced_orthogonality {R k : Type*} [CommRing R] [Field k]
    (c : R →+* ℂ) (hc : Function.Injective c) (r : R →+* k)
    (σ : Representation R G (Fin n → R))
    [IsIrreducible (mapCoefficients c σ)]
    (hn : 0 < n) (horder : Nat.card G = n * q) (a b i j : Fin n) :
    (∑ g : G, LinearMap.toMatrix' (mapCoefficients r σ g⁻¹) j i *
      LinearMap.toMatrix' (mapCoefficients r σ g) a b) =
      (q : k) * (if a = i then 1 else 0) * (if b = j then 1 else 0) := by
  classical
  have hR : (∑ g : G, LinearMap.toMatrix' (σ g⁻¹) j i * LinearMap.toMatrix' (σ g) a b) =
      (q : R) * (if a = i then 1 else 0) * (if b = j then 1 else 0) := by
    apply hc
    simpa only [map_sum, map_mul, map_natCast, apply_ite, map_one, map_zero,
      mapCoefficients_toMatrix, Matrix.map_apply] using
      coefficient_orthogonality (mapCoefficients c σ) hn horder a b i j
  simpa only [map_sum, map_mul, map_natCast, apply_ite, map_one, map_zero,
    mapCoefficients_toMatrix, Matrix.map_apply] using congrArg r hR

private theorem irreducible_of_orthogonality {k : Type*} [Field k]
    (ρ : Representation k G (Fin n → k)) (hn : 0 < n) (hq : (q : k) ≠ 0)
    (horth : ∀ a b i j : Fin n,
      (∑ g : G, LinearMap.toMatrix' (ρ g⁻¹) j i * LinearMap.toMatrix' (ρ g) a b) =
        (q : k) * (if a = i then 1 else 0) * (if b = j then 1 else 0)) :
    IsIrreducible ρ := by
  classical
  have : NeZero n := ⟨hn.ne'⟩
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · exact ⟨⟨⊥, ⊤, fun h => (bot_ne_top : (⊥ : Submodule k (Fin n → k)) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule h)⟩⟩
  · intro W
    by_cases hW : W = ⊥
    · exact Or.inl hW
    right
    have hW' : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.toSubmodule_injective h)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx0
    have he (i : Fin n) : Pi.single i (1 : k) ∈ W.toSubmodule := by
      have hs : (∑ g : G, LinearMap.toMatrix' (ρ g⁻¹) j i • ρ g) x ∈ W.toSubmodule := by
        rw [LinearMap.sum_apply]
        exact Submodule.sum_mem _ fun g _ =>
          W.toSubmodule.smul_mem _ (W.apply_mem_toSubmodule g hx)
      rw [matrix_unit_sum ρ horth i j] at hs
      change (q : k) • (x j • Pi.single i (1 : k)) ∈ W.toSubmodule at hs
      exact (W.toSubmodule.smul_mem_iff hj).mp ((W.toSubmodule.smul_mem_iff hq).mp hs)
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro y _
    rw [← Finset.univ_sum_single y]
    apply Submodule.sum_mem
    intro i _
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using
      W.toSubmodule.smul_mem (y i) (he i)

end DefectZeroReduction

/-- A genuine coefficient reduction of an ordinary irreducible representation
is irreducible whenever the quotient of the group order by its degree is
nonzero in the residue field. The integral representation remains an explicit
input; no integral-model existence or modular irreducibility is assumed. -/
theorem isIrreducible_mapCoefficients_of_defectZero
    {R k G : Type*} [CommRing R] [Field k] [Group G] [Finite G] {n q : ℕ}
    (c : R →+* ℂ) (hc : Function.Injective c) (r : R →+* k)
    (σ : Representation R G (Fin n → R))
    (hσ : IsIrreducible (mapCoefficients c σ))
    (hn : 0 < n) (horder : Nat.card G = n * q) (hq : (q : k) ≠ 0) :
    IsIrreducible (mapCoefficients r σ) := by
  let : Fintype G := Fintype.ofFinite G
  let := hσ
  exact DefectZeroReduction.irreducible_of_orthogonality (mapCoefficients r σ) hn hq
    (DefectZeroReduction.reduced_orthogonality c hc r σ hn horder)

end Representation
