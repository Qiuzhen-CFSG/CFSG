module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Automorphisms of the binary three-dimensional linear group

Every automorphism of GL₃(2) is inner or inverse transpose times inner.
The actual projective-to-linear equivalence transports the known orders
|GL₃(2)| = 168 and |Aut(GL₃(2))| = 336 and the triviality of the center,
so the subgroup of inner automorphisms has index two.

To identify its other coset, consider the companion matrix of X³ + X + 1.
It has trace zero, whereas its inverse transpose has trace one. Since
conjugation preserves trace, the actual `OuterCyclic.graphLinear 3` is
not inner. The two-coset argument then gives the asserted coverage.

This is the dimension-three automorphism input to the invariant minimal
parabolic argument in Aschbacher–Smith 13.8.25, printed p.959 of
`refs/quasithin.pdf`, rather than the whole source lemma. It is also the
binary dimension-three specialization of GLS3 Theorem 2.5.12(a–e,i),
with the inverse-transpose formula in §2.7 (`refs/KGroup/GLS3/chapter2.tex`).
The source's graph representative differs from pure inverse transpose by
an inner automorphism, which does not change the asserted two cosets.
-/

public section

open scoped MatrixGroups
namespace BinaryLinear.InvariantNodeActions.ThreeAutomorphisms
open OuterCyclic

private def traceWitness : SL(3, ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], by decide⟩

private theorem traceWitness_trace :
    Matrix.trace (traceWitness : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by decide

private theorem traceWitness_graph_trace :
    Matrix.trace (graphSL 3 traceWitness : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by decide

private theorem trace_conj (g A : SL(3, ZMod 2)) :
    Matrix.trace (↑(g * A * g⁻¹) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      Matrix.trace (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  change Matrix.trace ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
    (↑(g⁻¹) : Matrix (Fin 3) (Fin 3) (ZMod 2))) = _
  rw [Matrix.trace_mul_cycle]
  change Matrix.trace (↑((g⁻¹ * g) * A) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
  rw [inv_mul_cancel, one_mul]

/-- Inverse transpose is not inner in binary dimension three. -/
theorem graphLinear_ne_conj (g : LinearGroup 3) : graphLinear 3 ≠ MulAut.conj g := by
  intro h
  let g' := (slEquivLinear 3).symm g
  have hA : graphSL 3 traceWitness = g' * traceWitness * g'⁻¹ := by
    apply (slEquivLinear 3).injective
    change slEquivLinear 3 (Matrix.SpecialLinearGroup.transpose traceWitness)⁻¹ = _
    rw [← graphLinear_slEquivLinear, h]
    simp only [MulAut.conj_apply, map_mul, map_inv, g', MulEquiv.apply_symm_apply]
  have he := congrArg (fun A : SL(3, ZMod 2) => Matrix.trace
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2))) hA
  rw [trace_conj, traceWitness_trace, traceWitness_graph_trace] at he
  exact one_ne_zero he

private theorem center_linear_eq_bot : Subgroup.center (LinearGroup 3) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have h := ((Subgroup.centerCongr (projectiveEquivLinear (by decide : 0 < 3))).symm
    ⟨x, hx⟩).property
  change (projectiveEquivLinear (by decide : 0 < 3)).symm x ∈
    Subgroup.center Matrix.PSL3Two.PSL at h
  have heq : (projectiveEquivLinear (by decide : 0 < 3)).symm x = 1 :=
    Subgroup.mem_bot.mp (Matrix.PSL3Two.Automorphisms.center_psl_eq_bot.le h)
  exact Subgroup.mem_bot.mpr ((projectiveEquivLinear (by decide : 0 < 3)).symm.map_eq_one_iff.mp heq)

private theorem card_linear : Nat.card (LinearGroup 3) = 168 := by
  rw [← Nat.card_congr (projectiveEquivLinear (by decide : 0 < 3)).toEquiv]
  exact Matrix.PSL3Two.card_PSL

private theorem card_aut : Nat.card (MulAut (LinearGroup 3)) = 336 := by
  rw [← Nat.card_congr (MulAut.congr (projectiveEquivLinear (by decide : 0 < 3))).toEquiv]
  exact Matrix.PSL3Two.Automorphisms.card_aut

private theorem inner_index : (MulAut.innerSubgroup (LinearGroup 3)).index = 2 := by
  have hc : Nat.card (MulAut.innerSubgroup (LinearGroup 3)) = 168 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (MulAut.conj_injective_of_center_eq_bot center_linear_eq_bot)).toEquiv]
    exact card_linear
  have hi := (MulAut.innerSubgroup (LinearGroup 3)).index_mul_card
  rw [hc, card_aut] at hi
  omega

/-- Every automorphism of GL₃(2) is inner or inverse transpose times inner. -/
theorem inner_graph (a : MulAut (LinearGroup 3)) :
    ∃ g : LinearGroup 3, a = MulAut.conj g ∨ a = graphLinear 3 * MulAut.conj g := by
  by_cases ha : a ∈ MulAut.innerSubgroup (LinearGroup 3)
  · obtain ⟨g, rfl⟩ := ha
    exact ⟨g, Or.inl rfl⟩
  · have hn : graphLinear 3 ∉ MulAut.innerSubgroup (LinearGroup 3) := by
      rintro ⟨g, hg⟩
      exact graphLinear_ne_conj g hg.symm
    have hga : graphLinear 3 * a ∈ MulAut.innerSubgroup (LinearGroup 3) :=
      (Subgroup.mul_mem_iff_of_index_two inner_index).mpr (iff_of_false hn ha)
    obtain ⟨g, hg⟩ := hga
    refine ⟨g, Or.inr ?_⟩
    calc
      a = (graphLinear 3 * graphLinear 3) * a := by
        rw [← pow_two, graphLinear_sq, one_mul]
      _ = graphLinear 3 * MulAut.conj g := by rw [mul_assoc, ← hg]

end BinaryLinear.InvariantNodeActions.ThreeAutomorphisms
