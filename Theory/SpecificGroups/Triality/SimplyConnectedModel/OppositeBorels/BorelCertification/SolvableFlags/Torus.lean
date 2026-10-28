module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.BorelCertification.Triangular

/-!
# Coordinate projections for subspaces invariant under the coroot torus

Surjectivity of the coroot diagonal parameters gives every ordinary diagonal
isometry. For a diagonal acting on one hyperbolic pair, a quadratic polynomial
in that operator projects onto either coordinate line. A scalar different from
zero and one has distinct reciprocal in characteristic two. The resulting
projectors preserve each torus-invariant subspace, and hence each subspace
invariant under a signed torus-and-root candidate.

This supplies the weight-space step in the proof of GLS3, 1.11.2
(`refs/KGroup/GLS3/Chapter1.tex`), specialized to the natural D4 module.
-/

@[expose] public section
open Theory Theory.AlgebraicGroup
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.NaturalCoefficients
noncomputable section
namespace Triality.SimplyConnected.OppositeBorels.BorelCertification.SolvableFlags
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

private lemma exists_separating_unit : ∃ a : kˣ, (a : k) ≠ 1 ∧ (a : k) ≠ (a : k)⁻¹ := by
  classical
  obtain ⟨x, hx⟩ := (Finset.exists_notMem ({0, 1} : Finset k))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  refine ⟨Units.mk0 x hx.1, hx.2, ?_⟩
  change x ≠ x⁻¹
  intro he
  apply hx.2
  apply CharTwo.sq_injective
  calc
    x ^ 2 = x⁻¹ * x := by rw [pow_two, ← he]
    _ = 1 ^ 2 := by rw [inv_mul_cancel₀ hx.1, one_pow]

omit [IsAlgClosed k] [CharP k 2] in
private lemma diagonal_projector (a : kˣ) (i : Fin 4) (v : QuadraticSpace k) :
    let D := (hyperbolicDiagonalPoint 4 (Function.update (fun _ => 1) i a)).1
    D (D v - v) - (a : k)⁻¹ • (D v - v) =
      (((a : k) - (a : k)⁻¹) * ((a : k) - 1)) •
        ((basis k).coord (.inl i) v • basis k (.inl i)) := by
  classical
  dsimp only
  rw [basis_coord_inl]
  ext j <;> by_cases hj : j = i <;>
    simp [basis_apply, hyperbolicDiagonalPoint,
      hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
      Function.update_apply, hj, Pi.smul_apply, smul_eq_mul]
  ring

lemma upper_coordinate_mem_of_diagonal_invariant (W : Submodule k (QuadraticSpace k))
    (hW : ∀ (d : Fin 4 → kˣ) v, v ∈ W → (hyperbolicDiagonalPoint 4 d).1 v ∈ W)
    (v : QuadraticSpace k) (hv : v ∈ W) (i : Fin 4) :
    (basis k).coord (.inl i) v • basis k (.inl i) ∈ W := by
  obtain ⟨a, ha1, hainv⟩ := exists_separating_unit k
  let d : Fin 4 → kˣ := Function.update (fun _ => 1) i a
  let D := (hyperbolicDiagonalPoint 4 d).1
  have hw : D v - v ∈ W := W.sub_mem (hW d v hv) hv
  have hy := W.sub_mem (hW d (D v - v) hw) (W.smul_mem (a : k)⁻¹ hw)
  have he := diagonal_projector k a i v
  change D (D v - v) - (a : k)⁻¹ • (D v - v) = _ at he
  rw [he] at hy
  have hc : ((a : k) - (a : k)⁻¹) * ((a : k) - 1) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hainv) (sub_ne_zero.mpr ha1)
  have hh := W.smul_mem ((((a : k) - (a : k)⁻¹) * ((a : k) - 1))⁻¹) hy
  simpa only [smul_smul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hh

omit [IsAlgClosed k] [CharP k 2] in
private lemma diagonal_projector_lower (a : kˣ) (i : Fin 4) (v : QuadraticSpace k) :
    let D := (hyperbolicDiagonalPoint 4 (Function.update (fun _ => 1) i a)).1
    D (D v - v) - (a : k) • (D v - v) =
      (((a : k)⁻¹ - (a : k)) * ((a : k)⁻¹ - 1)) •
        ((basis k).coord (.inr i) v • basis k (.inr i)) := by
  classical
  dsimp only
  rw [basis_coord_inr]
  ext j <;> by_cases hj : j = i <;>
    simp [basis_apply, hyperbolicDiagonalPoint,
      hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
      Function.update_apply, hj, Pi.smul_apply, smul_eq_mul]
  ring

lemma lower_coordinate_mem_of_diagonal_invariant (W : Submodule k (QuadraticSpace k))
    (hW : ∀ (d : Fin 4 → kˣ) v, v ∈ W → (hyperbolicDiagonalPoint 4 d).1 v ∈ W)
    (v : QuadraticSpace k) (hv : v ∈ W) (i : Fin 4) :
    (basis k).coord (.inr i) v • basis k (.inr i) ∈ W := by
  obtain ⟨a, ha1, hainv⟩ := exists_separating_unit k
  let d : Fin 4 → kˣ := Function.update (fun _ => 1) i a
  let D := (hyperbolicDiagonalPoint 4 d).1
  have hw : D v - v ∈ W := W.sub_mem (hW d v hv) hv
  have hy := W.sub_mem (hW d (D v - v) hw) (W.smul_mem (a : k) hw)
  have he := diagonal_projector_lower k a i v
  change D (D v - v) - (a : k) • (D v - v) = _ at he
  rw [he] at hy
  have hc : ((a : k)⁻¹ - (a : k)) * ((a : k)⁻¹ - 1) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hainv.symm) (sub_ne_zero.mpr (by simpa using ha1))
  have hh := W.smul_mem ((((a : k)⁻¹ - (a : k)) * ((a : k)⁻¹ - 1))⁻¹) hy
  simpa only [smul_smul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hh

lemma coordinate_mem_of_torus_invariant (W : Submodule k (QuadraticSpace k))
    (hW : ∀ g ∈ CorootTorus.closedSubgroup k, ∀ v ∈ W, (naturalAction k g).1 v ∈ W)
    (v : QuadraticSpace k) (hv : v ∈ W) (p : Index) :
    (basis k).coord p v • basis k p ∈ W := by
  have hd : ∀ (d : Fin 4 → kˣ) v, v ∈ W → (hyperbolicDiagonalPoint 4 d).1 v ∈ W := by
    intro d v hv
    obtain ⟨t, rfl⟩ := CorootTorus.diagonal_surjective k d
    simpa only [CorootTorus.naturalAction_parameter] using
      hW (CorootTorus.parameter k t) (CorootTorus.parameter_mem k t) v hv
  cases p with
  | inl i => exact upper_coordinate_mem_of_diagonal_invariant k W hd v hv i
  | inr i => exact lower_coordinate_mem_of_diagonal_invariant k W hd v hv i

lemma coordinate_mem_of_candidate_invariant (negative : Bool)
    (W : Submodule k (QuadraticSpace k))
    (hW : ∀ g ∈ candidate k negative, ∀ v ∈ W, (naturalAction k g).1 v ∈ W)
    (v : QuadraticSpace k) (hv : v ∈ W) (p : Index) :
    (basis k).coord p v • basis k p ∈ W :=
  coordinate_mem_of_torus_invariant k W
    (fun g hg => hW g (torus_le_torusRootGenerated k (signedRoots k negative) hg)) v hv p

end Triality.SimplyConnected.OppositeBorels.BorelCertification.SolvableFlags
