module

public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm
public import Theory.SpecificGroups.PSL3Three.Simplicity
public import Theory.SpecificGroups.PSL3Three.Basic
/-!
# Inner and graph automorphisms of PSL₃(3)

Over the three-element field every unit equals its cube. Multiplying a GL₃
actor by the inverse determinant scalar therefore gives an SL₃ actor with
exactly the same conjugation action on the canonical projective quotient.
The proved odd-prime automorphism normal form then covers every automorphism
by an inner automorphism or an inner automorphism times inverse transpose.

This supplies the full-coverage input to the graph-centralizer product in
`EightCentralizers.GraphModel` and its elementary-eight consumer.
Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2,
manuscript p.10; standard automorphisms as in GLS3, Theorem 2.5.12(a).
-/

public section

open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OddInvolutionFixed
namespace Matrix.PSL3Three.GraphWitnesses.EightCentralizers.GraphModel
private theorem unit_cube (u : (ZMod 3)ˣ) : u ^ 3 = u := by
  apply Units.ext
  exact (by decide : ∀ z : ZMod 3, z ^ 3 = z) u.val

theorem linearConj_inner (g : GL (Fin 3) (ZMod 3)) :
    ∃ x : PSL, linearConj (ZMod 3) g = MulAut.conj x := by
  let m := GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det g)⁻¹ * g
  have hm : GeneralLinearGroup.det m = 1 := by
    simp only [m, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin,
      unit_cube, inv_mul_cancel]
  let x := (slEquivDetKernel (ZMod 3)).symm ⟨m, hm⟩
  refine ⟨project x, ?_⟩
  calc
    linearConj (ZMod 3) g = linearConj (ZMod 3) m := by
      dsimp only [m]
      rw [map_mul, linearConj_scalar, one_mul]
    _ = linearConj (ZMod 3) (SpecialLinearGroup.toGL x) := by
      rw [slEquivDetKernel_symm_toGL]
    _ = MulAut.conj (project x) := linearConj_toGL (ZMod 3) x

theorem automorphism_inner_or_inner_graph (a : MulAut PSL) :
    ∃ x : PSL, a = MulAut.conj x ∨ a = MulAut.conj x * graph (ZMod 3) := by
  let : IsSimpleGroup PSL := isSimpleGroup_psl3_three
  obtain ⟨g, hg | hg⟩ := automorphism_normal_form not_isSolvable_psl3_three
    Nat.prime_three (by decide) (by simp) a
  · obtain ⟨x, hx⟩ := linearConj_inner g
    exact ⟨x, Or.inl (hg.trans hx)⟩
  · obtain ⟨x, hx⟩ := linearConj_inner g
    exact ⟨x, Or.inr (hg.trans (congrArg (· * graph (ZMod 3)) hx))⟩
end Matrix.PSL3Three.GraphWitnesses.EightCentralizers.GraphModel
