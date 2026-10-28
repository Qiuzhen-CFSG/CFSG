module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorOrthogonal
public import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Simplicity of the binary exterior four-space

Two differences of elementary transvections isolate any specified nonzero
wedge coefficient. Further transvection differences carry the resulting basis
vector to every wedge basis vector. Thus the actual second-compound action of
SL₄(F₂) is simple. The transvection formulas are checked separately, keeping
nested compound-matrix expansion out of the simplicity argument.

This is the simplicity input for the six-dimensional orthogonal alternative
in Aschbacher--Smith, C.4.8, printed p.154, and B.4.2(10), printed p.86.
The compound action is the attributed ATLAS model imported above.
-/

@[expose] public noncomputable section
open Atlas.Order20160A8.Bivectors
open scoped MatrixGroups
namespace Representation.BinaryParabolicExteriorSquare
abbrev Bit := ZMod 2
abbrev Six := Fin 6 → Bit
private def delta (i j : Fin 4) (x : Six) : Six :=
  exteriorMap (Matrix.transvection i j (1 : Bit)) x - x

private def opposite : Fin 6 → Fin 6 := ![5,4,3,2,1,0]

private theorem delta_01 (x : Six) : delta 0 1 x = ![0,x 3,x 4,0,0,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;> ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_02 (x : Six) : delta 0 2 x = ![x 3,0,x 5,0,0,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;> ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_10 (x : Six) : delta 1 0 x = ![0,0,0,x 1,x 2,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;> ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_13 (x : Six) : delta 1 3 x = ![x 2,0,0,x 5,0,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;> ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_20 (x : Six) : delta 2 0 x = ![0,0,0,x 0,0,x 2] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;> ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_23 (x : Six) : delta 2 3 x = ![0,x 2,0,x 4,0,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;> ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_31 (x : Six) : delta 3 1 x = ![0,0,x 0,0,0,x 3] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;> ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_32 (x : Six) : delta 3 2 x = ![0,0,x 1,0,x 3,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;> ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem extract (s : Fin 6) (x : Six) :
    delta (first (opposite s)) (first s)
      (delta (second (opposite s)) (second s) x) = x s • Pi.single (opposite s) 1 := by
  fin_cases s
  · change delta 2 0 (delta 3 1 x) = x 0 • Pi.single (5 : Fin 6) 1
    rw [delta_31, delta_20]
    ext t
    fin_cases t <;> simp
  · change delta 1 0 (delta 3 2 x) = x 1 • Pi.single (4 : Fin 6) 1
    rw [delta_32, delta_10]
    ext t
    fin_cases t <;> simp
  · change delta 1 0 (delta 2 3 x) = x 2 • Pi.single (3 : Fin 6) 1
    rw [delta_23, delta_10]
    ext t
    fin_cases t <;> simp
  · change delta 0 1 (delta 3 2 x) = x 3 • Pi.single (2 : Fin 6) 1
    rw [delta_32, delta_01]
    ext t
    fin_cases t <;> simp
  · change delta 0 1 (delta 2 3 x) = x 4 • Pi.single (1 : Fin 6) 1
    rw [delta_23, delta_01]
    ext t
    fin_cases t <;> simp
  · change delta 0 2 (delta 1 3 x) = x 5 • Pi.single (0 : Fin 6) 1
    rw [delta_13, delta_02]
    ext t
    fin_cases t <;> simp

private theorem delta_mem (P : Submodule Bit Six)
    (hP : ∀ g : SL(4, Bit), ∀ x ∈ P, exteriorMap g.val x ∈ P)
    (i j : Fin 4) (hij : i ≠ j) {x : Six} (hx : x ∈ P) : delta i j x ∈ P :=
  P.sub_mem (hP (Matrix.SpecialLinearGroup.transvection hij 1) x hx) hx



private theorem basis_delta (i j : Fin 4) (s : Fin 6) :
    delta i j (Pi.single s 1) =
      fun t => (Matrix.transvection i j (1 : Bit)) (first t) (first s) *
        (Matrix.transvection i j (1 : Bit)) (second t) (second s) -
        (Matrix.transvection i j (1 : Bit)) (first t) (second s) *
        (Matrix.transvection i j (1 : Bit)) (second t) (first s) -
        (Pi.single s 1 : Six) t := by
  ext t
  simp [delta, exteriorMap, compound, Matrix.toLin'_apply]

private theorem basis_all (P : Submodule Bit Six)
    (hP : ∀ g : SL(4, Bit), ∀ x ∈ P, exteriorMap g.val x ∈ P)
    {s : Fin 6} (hs : (Pi.single s 1 : Six) ∈ P) :
    ∀ t : Fin 6, (Pi.single t 1 : Six) ∈ P := by
  have h0 : (Pi.single 0 1 : Six) ∈ P := by
    fin_cases s
    · exact hs
    · have h := delta_mem P hP 1 2 (by decide) hs
      convert h using 1; ext t; fin_cases t <;>
        simp [basis_delta, first, second, Matrix.transvection, Matrix.single]
    · have h := delta_mem P hP 1 3 (by decide) hs
      convert h using 1; ext t; fin_cases t <;>
        simp [basis_delta, first, second, Matrix.transvection, Matrix.single]
    · have h := delta_mem P hP 0 2 (by decide) hs
      convert h using 1; ext t; fin_cases t <;>
        simp [basis_delta, first, second, Matrix.transvection, Matrix.single]
    · have h := delta_mem P hP 0 3 (by decide) hs
      convert h using 1; ext t; fin_cases t <;>
        simp [basis_delta, first, second, Matrix.transvection, Matrix.single]
    · have he : delta 1 2 (Pi.single 5 1) = (Pi.single 4 1 : Six) := by
        ext t; fin_cases t <;>
          simp [basis_delta, first, second, Matrix.transvection, Matrix.single]
      have h4 := delta_mem P hP 1 2 (by decide) hs
      change delta 1 2 (Pi.single (5 : Fin 6) 1) ∈ P at h4
      rw [he] at h4
      have h := delta_mem P hP 0 3 (by decide) h4
      convert h using 1; ext t; fin_cases t <;>
        simp [basis_delta, first, second, Matrix.transvection, Matrix.single]
  have h1 : (Pi.single 1 1 : Six) ∈ P := by
    have h := delta_mem P hP 2 1 (by decide) h0
    convert h using 1; ext t; fin_cases t <;>
      simp [basis_delta, first, second, Matrix.transvection, Matrix.single]
  intro t
  fin_cases t
  · exact h0
  · exact h1
  · have h := delta_mem P hP 3 1 (by decide) h0
    convert h using 1; ext t; fin_cases t <;>
      simp [basis_delta, first, second, Matrix.transvection, Matrix.single]
  · have h := delta_mem P hP 2 0 (by decide) h0
    convert h using 1; ext t; fin_cases t <;>
      simp [basis_delta, first, second, Matrix.transvection, Matrix.single]
  · have h := delta_mem P hP 3 0 (by decide) h0
    convert h using 1; ext t; fin_cases t <;>
      simp [basis_delta, first, second, Matrix.transvection, Matrix.single]
  · have h := delta_mem P hP 3 0 (by decide) h1
    convert h using 1; ext t; fin_cases t <;>
      simp [basis_delta, first, second, Matrix.transvection, Matrix.single]

/-- Every nonzero invariant subspace of the binary exterior four-space is all of it. -/
theorem six_simple (P : Submodule Bit Six)
    (hP : ∀ g : SL(4, Bit), ∀ x ∈ P, exteriorMap g.val x ∈ P)
    (hne : P ≠ ⊥) : P = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff P).mp hne
  obtain ⟨s, hs⟩ : ∃ s, x s ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (funext h)
  have hs1 : x s = 1 :=
    ((by decide : ∀ c : Bit, c = 0 ∨ c = 1) (x s)).resolve_left hs
  have hi : first (opposite s) ≠ first s := by fin_cases s <;> decide
  have hj : second (opposite s) ≠ second s := by fin_cases s <;> decide
  have he := delta_mem P hP _ _ hi (delta_mem P hP _ _ hj hx)
  rw [extract, hs1, one_smul] at he
  have hb := basis_all P hP he
  apply top_unique
  intro v _
  rw [← (Pi.basisFun Bit (Fin 6)).sum_repr v]
  apply Submodule.sum_mem
  intro i _
  exact P.smul_mem _ (by simpa only [Pi.basisFun_apply] using hb i)

/-- A specific elementary transvection acts nontrivially on the six-space. -/
theorem six_transvection_nontrivial :
    exteriorMap (Matrix.transvection 0 2 (1 : Bit)) (Pi.single 3 1) ≠ (Pi.single 3 1 : Six) := by
  intro h
  have hd : delta 0 2 (Pi.single 3 1) = 0 := sub_eq_zero.mpr h
  have hc := congrFun hd 0
  norm_num [delta_02] at hc

end Representation.BinaryParabolicExteriorSquare
