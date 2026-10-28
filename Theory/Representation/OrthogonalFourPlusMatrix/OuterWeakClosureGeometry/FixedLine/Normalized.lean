module
public import Theory.Representation.OrthogonalFourPlusMatrix.OuterWeakClosureGeometry.FixedLine.Canonical
import Mathlib.Tactic.FinCases

/-!
# Transport from an upper triangular fixed vector

If a determinant isometry group fixes both the upper nilpotent matrix unit
and a nonsingular upper triangular matrix `u`, left multiplication by `u`
transports it to the canonical group fixing the identity and the nilpotent
unit. Its determinant rescales by the fixed nonzero factor `det u`.

The canonical pointwise kernel and moved vectors then transport back to the
original action. The resulting binary subspace has pointwise-kernel index
at most four, and its actual moved span contains nonsingular vectors on
two distinct field lines. Both quotient index and movement retain the
original actor, rather than passing to an unspecified isomorphic group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Lemma 9.4.5, printed pp.736–737.
-/

@[expose] public noncomputable section
open Matrix Module
namespace ClassicalOrthogonal.FourPlusMatrix.Binary.OuterWeakClosureGeometry.FixedLine.Normalized
open Canonical

variable {B : Type*} [Group B]

/-- The actual binary span of an actor's displacements on a subspace. -/
def movedSpace (f : B →* (V ≃ₗ[F] V)) (U : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {w | ∃ b : B, ∃ v ∈ U, f b v - v = w}

/-- Transport the canonical fixed-hyperplane geometry through a determinant similarity. -/
theorem geometry_of_coordinates (f : B →* (V ≃ₗ[F] V)) (hf : Function.Injective f)
    (hdet : ∀ b M, (f b M).det = M.det) (hcard : 8 ≤ Nat.card B)
    (e : V ≃ₗ[F] V) (d : F) (hd : d ≠ 0)
    (he : ∀ M, (e M).det = d * M.det)
    (hI : ∀ b, f b (e 1) = e 1) (hN : ∀ b, f b (e N) = e N) :
    ∃ U : Submodule (ZMod 2) V, ∃ K : Subgroup B,
      K.index ≤ 4 ∧ (∀ b ∈ K, ∀ v ∈ U, f b v = v) ∧
      ∃ x ∈ movedSpace f U, ∃ y ∈ movedSpace f U,
        x.det ≠ 0 ∧ y.det ≠ 0 ∧ y ∉ Submodule.span F ({x} : Set V) := by
  let g : B →* (V ≃ₗ[F] V) := (MulAut.conj e.symm).toMonoidHom.comp f
  have hg (b : B) (M : V) : g b M = e.symm (f b (e M)) := rfl
  have hgf : Function.Injective g := (MulAut.conj e.symm).injective.comp hf
  have hgd (b : B) (M : V) : (g b M).det = M.det := by
    apply mul_left_cancel₀ hd
    calc
      d * (g b M).det = (e (g b M)).det := (he _).symm
      _ = (f b (e M)).det := by rw [hg, e.apply_symm_apply]
      _ = (e M).det := hdet b _
      _ = d * M.det := he M
  have hgI (b : B) : g b (1 : V) = 1 := by rw [hg, hI, e.symm_apply_apply]
  have hgN (b : B) : g b N = N := by rw [hg, hN, e.symm_apply_apply]
  let eb := e.restrictScalars (ZMod 2)
  let U := (fixedHyperplane.restrictScalars (ZMod 2)).map eb.toLinearMap
  let K := pointwiseKernel g
  have hU (M : V) (hM : M ∈ fixedHyperplane) : e M ∈ U :=
    Submodule.mem_map.mpr ⟨M, hM, rfl⟩
  have hmove (b : B) (M : V) (hM : M ∈ fixedHyperplane) :
      e (g b M - M) ∈ movedSpace f U := by
    have hh : e (g b M - M) = f b (e M) - e M := by
      rw [map_sub, hg, e.apply_symm_apply]
    rw [hh]
    exact Submodule.subset_span ⟨b, e M, hU M hM, rfl⟩
  have hw := movement_witnesses g hgf hgd hgI hgN hcard
    ((movedSpace f U).comap eb.toLinearMap) (fun b M hM => hmove b M hM)
  refine ⟨U, K, pointwiseKernel_index_le_four g hgd hgI hgN, ?_,
    e 1, hw.1, e (1 + N), hw.2, ?_, ?_, ?_⟩
  · intro b hb v hv
    obtain ⟨M, hM, rfl⟩ := Submodule.mem_map.mp hv
    have hh := (mem_pointwiseKernel g b).mp hb M hM
    have hmap := congrArg e hh
    change f b (e M) = e M
    simpa only [hg, e.apply_symm_apply] using hmap
  · rw [he, witness_determinants.1, mul_one]
    exact hd
  · rw [he, witness_determinants.2, mul_one]
    exact hd
  · intro hy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    apply witnesses_noncollinear
    refine ⟨c, e.injective ?_⟩
    simpa only [map_smul] using hc

/-- A fixed upper triangular nonsingular vector provides the required coordinates. -/
theorem geometry_of_upper_fixed (f : B →* (V ≃ₗ[F] V)) (hf : Function.Injective f)
    (hdet : ∀ b M, (f b M).det = M.det) (hcard : 8 ≤ Nat.card B)
    (u : V) (hu : u.det ≠ 0) (hu10 : u 1 0 = 0)
    (hfix : ∀ b, f b u = u) (hN : ∀ b, f b N = N) :
    ∃ U : Submodule (ZMod 2) V, ∃ K : Subgroup B,
      K.index ≤ 4 ∧ (∀ b ∈ K, ∀ v ∈ U, f b v = v) ∧
      ∃ x ∈ movedSpace f U, ∃ y ∈ movedSpace f U,
        x.det ≠ 0 ∧ y.det ≠ 0 ∧ y ∉ Submodule.span F ({x} : Set V) := by
  let uu : Vˣ := Matrix.nonsingInvUnit u (isUnit_iff_ne_zero.mpr hu)
  let e := uu.mulLeftLinearEquiv F V
  have he (M : V) : e M = u * M := rfl
  have he1 : e 1 = u := by rw [he, mul_one]
  have heN : e N = u 0 0 • N := by
    rw [he]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [N, Matrix.mul_apply, hu10]
  apply geometry_of_coordinates f hf hdet hcard e u.det hu
  · intro M; rw [he, Matrix.det_mul]
  · intro b; rw [he1, hfix]
  · intro b; rw [heN, map_smul, hN]

end ClassicalOrthogonal.FourPlusMatrix.Binary.OuterWeakClosureGeometry.FixedLine.Normalized
