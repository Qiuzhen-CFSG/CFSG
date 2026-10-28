module

public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.ThreeAutomorphisms
import Mathlib.Tactic.Group

/-!
# Singer commutators of outer involutions of SL₃(2)

The checked inner/graph automorphism dichotomy writes an outer automorphism
as inverse transpose followed by conjugation. Its square being one makes the
conjugating matrix symmetric, since SL₃(2) is centerless. A finite binary matrix
calculation supplies a Gram factorization g = hᵀh. Conjugating a cube of the
specified symmetric Singer matrix then gives the required commutator.

The finite calculations use kernel-checked decision proofs on literal matrices.
The automorphism input is the dimension-three specialization of GLS3,
Theorem 2.5.12 and §2.7, as documented in `ThreeAutomorphisms`. This witness is
used in Aschbacher–Smith 13.8.21(1), printed p.956 (1 March 2004 manuscript).
-/

@[expose] public section
namespace Matrix.PSL3Two.OuterInvolutionSinger
open BinaryLinear.OuterCyclic
open scoped MatrixGroups
set_option maxRecDepth 3000 in
set_option maxHeartbeats 800000 in
private theorem symmetric_gram : ∀ g : SL, g.transpose = g → ∃ h : SL, g = h.transpose * h := by
  decide +kernel

private theorem inner_graph (α : MulAut SL) : ∃ g : SL,
    α = MulAut.conj g ∨ α = graphSL 3 * MulAut.conj g := by
  obtain ⟨g, hg⟩ := BinaryLinear.InvariantNodeActions.ThreeAutomorphisms.inner_graph
    (MulAut.congr (slEquivLinear 3) α)
  obtain ⟨k, rfl⟩ := (slEquivLinear 3).surjective g
  refine ⟨k, ?_⟩
  rcases hg with hi | hg
  · left
    ext x : 1
    apply (slEquivLinear 3).injective
    have hh := congrArg (fun β : MulAut (LinearGroup 3) => β (slEquivLinear 3 x)) hi
    simpa using hh
  · right
    ext x : 1
    apply (slEquivLinear 3).injective
    have hh := congrArg (fun β : MulAut (LinearGroup 3) => β (slEquivLinear 3 x)) hg
    simpa [graphLinear] using hh

private theorem symmetric_of_sq (g : SL) (h : (graphSL 3 * MulAut.conj g) ^ 2 = 1) : g.transpose = g := by
  have hγ (x : SL) : graphSL 3 (graphSL 3 x) = x :=
    congrArg (fun a : MulAut SL => a x) (graphSL_sq 3)
  have he : MulAut.conj (graphSL 3 g * g) = (graphSL 3 * MulAut.conj g) ^ 2 := by
    ext x : 1
    simp only [pow_two, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hγ]
  have hh : graphSL 3 g * g = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot (binary_center_eq_bot (by decide : 0 < 3))
    rw [he, h, map_one]
  have hi : (g.transpose)⁻¹ = g⁻¹ := mul_eq_one_iff_eq_inv.mp hh
  exact inv_injective hi

/-- A symmetric Singer matrix in the actual special linear group. -/
def singer : SL := ⟨!![0,0,1; 0,1,1; 1,1,0], by decide⟩

private theorem commutator_of_gram (g h : SL) (hg : g = h.transpose * h) :
    ∃ b c : SL, (graphSL 3 * MulAut.conj g) b * b⁻¹ = c * singer * c⁻¹ := by
  have ht : graphSL 3 h.transpose = h⁻¹ := by
    change (h.transpose.transpose)⁻¹ = h⁻¹
    congr 1
  have hs : graphSL 3 (singer ^ 3) * (singer ^ 3)⁻¹ = singer := by decide
  refine ⟨h⁻¹ * singer ^ 3 * h, h⁻¹, ?_⟩
  rw [MulAut.mul_apply, MulAut.conj_apply, hg]
  calc
    graphSL 3 ((h.transpose * h) * (h⁻¹ * singer ^ 3 * h) * (h.transpose * h)⁻¹) *
        (h⁻¹ * singer ^ 3 * h)⁻¹ =
        h⁻¹ * (graphSL 3 (singer ^ 3) * (singer ^ 3)⁻¹) * h := by
      simp only [map_mul, map_inv, ht]
      group
    _ = h⁻¹ * singer * (h⁻¹)⁻¹ := by rw [hs, inv_inv]

/-- Every outer involutory automorphism has a commutator conjugate to the
specified Singer element. -/
theorem exists_commutator_conjugate_singer (α : MulAut SL)
    (ha : α ^ 2 = 1) (hout : ∀ g, α ≠ MulAut.conj g) :
    ∃ b c : SL, α b * b⁻¹ = c * singer * c⁻¹ := by
  obtain ⟨g, hg⟩ := inner_graph α
  rcases hg with hi | hi
  · exact False.elim (hout g hi)
  · have hs := symmetric_of_sq g (hi ▸ ha)
    obtain ⟨h, hh⟩ := symmetric_gram g hs
    rw [hi]
    exact commutator_of_gram g h hh
end Matrix.PSL3Two.OuterInvolutionSinger
