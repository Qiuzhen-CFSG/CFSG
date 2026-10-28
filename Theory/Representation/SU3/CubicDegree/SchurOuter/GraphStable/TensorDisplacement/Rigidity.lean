module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.Bounds
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Removing scalar ambiguity from the tensor model

On an irreducible representation over an algebraically closed field, two
operators inducing the same conjugation action differ by a scalar. If both
square to one in characteristic two, that scalar is one. The proof constructs
the actual commuting intertwiner and applies Schur's lemma, then uses both
square equations; no faithfulness of the component action is needed.

The consumer compares the literal actor with tensorwise transpose in specified
linear coordinates. Its remaining conjugation-covariance premise must come
from the outer-automorphism and matrix-coordinate argument. Once supplied,
the common invariant quotient satisfies `wordDegree ≤ 3 * codimension`.
Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32, together with §2.2 and §3.5.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation.SL3.BinaryDefiningFactors
namespace Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement
variable {K G V : Type*} [Field K] [IsAlgClosed K] [CharP K 2] [Monoid G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Schur scalar ambiguity vanishes for two square-one realizations of the same action. -/
theorem involutions_eq_of_conjugation_eq (ρ : Representation K G V) [ρ.IsIrreducible]
    (A B : Module.End K V) (hA : A * A = 1) (hB : B * B = 1)
    (hc : ∀ g, A * ρ g * A = B * ρ g * B) : A = B := by
  let f : IntertwiningMap ρ ρ := {
    toLinearMap := B * A
    isIntertwining' := by
      intro g
      change B * A * ρ g = ρ g * (B * A)
      calc
        B * A * ρ g = B * (A * ρ g * A) * A := by simp only [mul_assoc, hA, mul_one]
        _ = B * (B * ρ g * B) * A := by rw [hc]
        _ = ρ g * (B * A) := by simp only [← mul_assoc, hB, one_mul] }
  obtain ⟨c, hc⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).surjective f
  have hBA : B * A = c • (1 : Module.End K V) := by
    have h := congrArg IntertwiningMap.toLinearMap hc.symm
    change B * A = c • (1 : Module.End K V) at h
    exact h
  have he : A = c • B := by
    have h := congrArg (fun T : Module.End K V => B * T) hBA
    simpa only [← mul_assoc, hB, one_mul, mul_smul_comm, mul_one] using h
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hs : c ^ 2 = 1 := by
    apply smul_left_injective K (one_ne_zero : (1 : Module.End K V) ≠ 0)
    change c ^ 2 • (1 : Module.End K V) = (1 : K) • (1 : Module.End K V)
    rw [one_smul]
    have h := hA
    rw [he, smul_mul_smul_comm, hB, ← pow_two] at h
    exact h
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hs with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  simpa only [hc1, one_smul] using he

/-- The canonical tensor transpose transported through actual linear coordinates. -/
@[expose] def wordTransposeInCoordinates {w : List Factor} (e : V ≃ₗ[K] WordSpace K w) :
    Module.End K V :=
  e.symm.toLinearMap.comp ((wordTranspose w).comp e.toLinearMap)

omit [IsAlgClosed K] [CharP K 2] [FiniteDimensional K V] in
/-- The transported model operator is still square-one. -/
theorem wordTransposeInCoordinates_sq {w : List Factor} (e : V ≃ₗ[K] WordSpace K w) :
    wordTransposeInCoordinates e * wordTransposeInCoordinates e = 1 := by
  apply LinearMap.ext
  intro v
  change e.symm (wordTranspose w (e (e.symm (wordTranspose w (e v))))) = v
  rw [e.apply_symm_apply]
  have h := LinearMap.congr_fun (wordTranspose_sq (K := K) w) (e v)
  change wordTranspose w (wordTranspose w (e v)) = e v at h
  rw [h, e.symm_apply_apply]

variable {H : Type*} [Group H]

/-- Conjugation covariance suffices: irreducibility and square-one identify the operators,
then the tensor estimate bounds the literal common invariant quotient. -/
theorem wordDegree_le_three_invariants_quotient_of_conjugation
    (ρ : Representation K G V) [ρ.IsIrreducible]
    (τ : Representation K H V) (a : H) (ha2 : τ a * τ a = 1)
    (w : List Factor) (hn : naturalCount w = 0) (ha : 0 < adjointCount w)
    (e : V ≃ₗ[K] WordSpace K w)
    (hc : ∀ g, τ a * ρ g * τ a =
      wordTransposeInCoordinates e * ρ g * wordTransposeInCoordinates e) :
    wordDegree w ≤ 3 * Module.finrank K (V ⧸ τ.invariants) := by
  have heq := involutions_eq_of_conjugation_eq ρ (τ a)
    (wordTransposeInCoordinates e) ha2 (wordTransposeInCoordinates_sq e) hc
  apply wordDegree_le_three_invariants_quotient τ a w hn ha e
  intro v
  rw [heq]
  exact e.apply_symm_apply (wordTranspose w (e v))

end Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement
