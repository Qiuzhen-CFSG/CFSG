module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/SingularAction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Theory.AtlasPort.LinearGroups.G2.SingularPoints
public import Mathlib.LinearAlgebra.Projectivization.Action

@[expose] public section

/-!
# Faithfulness of the singular-point action

A kernel element scales each of the six off-diagonal singular basis vectors.
Five singular sums connect these vectors and force one common scalar c.
Their nonzero products force c²=c, hence c=1, and then determine the other
two basis vectors. This argument uses neither group order nor simplicity,
and applies in every characteristic, including two and three.
-/
noncomputable section

namespace Atlas.G2
open Atlas.SplitOctonion
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F]

instance singularPointsAction : MulAction (Model F) (SingularPoints F) where
  smul g p := ⟨g.val • p.val, by
    rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk]
    apply (Atlas.LinearAlgebra.cone_mk_iff
      (fun x : Carrier F => trace x = 0 ∧ SplitOctonion.norm x = 0)
      (singular_smul_iff F) _ _).mpr
    simpa only [LinearEquiv.smul_def, automorphism_trace, automorphism_norm] using p.prop⟩
  one_smul p := Subtype.ext (one_smul _ _)
  mul_smul g h p := Subtype.ext (mul_smul g.val h.val p.val)

theorem singularPointMk_smul (g : Model F) (x : Carrier F) (hx : x ≠ 0)
    (ht : trace x = 0) (hn : SplitOctonion.norm x = 0) :
    g • singularPointMk F x hx ht hn =
      singularPointMk F (g.val x)
        (fun h => hx (g.val.injective (h.trans (map_zero g.val).symm)))
        ((automorphism_trace g x).trans ht) ((automorphism_norm g x).trans hn) := rfl

/-- The six off-diagonal singular basis vectors. -/
def offDiagonalIndex : Fin 6 → Fin 8 := ![0,1,2,5,6,7]
def offDiagonalVector (i : Fin 6) : Carrier F := basisVector (offDiagonalIndex i)

theorem offDiagonal_singular (i : Fin 6) :
    trace (offDiagonalVector (F := F) i) = 0 ∧
      SplitOctonion.norm (offDiagonalVector (F := F) i) = 0 := by
  fin_cases i <;>
    simp [offDiagonalVector, offDiagonalIndex, trace, SplitOctonion.norm,
      basisVector]

/-- A line-fixing linear map has the same scalar on two basis vectors if it fixes their sum. -/
theorem basis_scalars_equal (g : Carrier F →ₗ[F] Carrier F) (i j : Fin 8)
    (hij : i ≠ j) (a b c : F)
    (hi : g (basisVector i) = a • basisVector i)
    (hj : g (basisVector j) = b • basisVector j)
    (hc : g (basisVector i + basisVector j) = c • (basisVector i + basisVector j)) :
    a = b := by
  rw [map_add, hi, hj] at hc
  have h1 := congrFun hc i
  have h2 := congrFun hc j
  simp [basisVector, hij, Ne.symm hij, Pi.smul_apply, smul_eq_mul] at h1 h2
  exact h1.trans h2.symm

/-- Fixing every singular line forces an actual octonion automorphism to be the identity. -/
theorem singular_lines_kernel_trivial (g : Model F)
    (hg : ∀ p : SingularPoints F, g • p = p) : g = 1 := by
  have hx : ∀ x : Carrier F, trace x = 0 → SplitOctonion.norm x = 0 →
      ∃ c : F, g.val x = c • x := by
    intro x ht hn
    by_cases hz : x = 0
    · subst x; exact ⟨1, by simp⟩
    · have h := congrArg Subtype.val (hg (singularPointMk F x hz ht hn))
      change g.val • Projectivization.mk F x hz = Projectivization.mk F x hz at h
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at h
      obtain ⟨c,hc⟩ := h
      exact ⟨c, hc.symm⟩
  choose c hc using fun i : Fin 6 =>
    hx (offDiagonalVector i) (offDiagonal_singular i).1 (offDiagonal_singular i).2
  have hpair (i j : Fin 6) (hij : offDiagonalIndex i ≠ offDiagonalIndex j)
      (ht : trace (offDiagonalVector (F := F) i + offDiagonalVector j) = 0)
      (hn : SplitOctonion.norm (offDiagonalVector (F := F) i + offDiagonalVector j) = 0) :
      c i = c j := by
    obtain ⟨d,hd⟩ := hx _ ht hn
    exact basis_scalars_equal g.val.toLinearMap _ _ hij _ _ _ (hc i) (hc j) hd
  have hc1 : c 1 = c 0 := hpair 1 0 (by decide)
    (by simp [offDiagonalVector,offDiagonalIndex,trace,basisVector])
    (by simp [offDiagonalVector,offDiagonalIndex,SplitOctonion.norm,basisVector])
  have hcommon (i : Fin 6) : c i = c 0 := by
    fin_cases i
    · rfl
    · exact hc1
    · exact hpair 2 0 (by decide)
        (by simp [offDiagonalVector,offDiagonalIndex,trace,basisVector])
        (by simp [offDiagonalVector,offDiagonalIndex,SplitOctonion.norm,basisVector])
    · exact hpair 3 0 (by decide)
        (by simp [offDiagonalVector,offDiagonalIndex,trace,basisVector])
        (by simp [offDiagonalVector,offDiagonalIndex,SplitOctonion.norm,basisVector])
    · exact hpair 4 0 (by decide)
        (by simp [offDiagonalVector,offDiagonalIndex,trace,basisVector])
        (by simp [offDiagonalVector,offDiagonalIndex,SplitOctonion.norm,basisVector])
    · exact (hpair 5 1 (by decide)
        (by simp [offDiagonalVector,offDiagonalIndex,trace,basisVector])
        (by simp [offDiagonalVector,offDiagonalIndex,SplitOctonion.norm,basisVector])).trans hc1
  have hscale (i : Fin 6) : g.val (offDiagonalVector i) = c 0 • offDiagonalVector i := by
    rw [hc, hcommon]
  have hc0 : c 0 ≠ 0 := by
    intro hz
    have hh := hscale 0
    rw [hz, zero_smul] at hh
    have hh' := g.val.injective (hh.trans (map_zero g.val).symm)
    have hcoord := congrFun hh' 0
    simp [offDiagonalVector, offDiagonalIndex, basisVector] at hcoord
  have hprod : mul (offDiagonalVector (F := F) 1) (offDiagonalVector 2) =
      -offDiagonalVector 0 := by
    funext i
    fin_cases i <;> simp [mul, offDiagonalVector, offDiagonalIndex, basisVector]
  have hp := automorphism_mul g (offDiagonalVector 1) (offDiagonalVector 2)
  rw [hprod, map_neg, hscale, hscale, hscale, SplitOctonion.smul_mul, SplitOctonion.mul_smul, hprod] at hp
  have hh := congrFun hp 0
  have he : c 0 = c 0 * c 0 := by
    simpa [offDiagonalVector, offDiagonalIndex, basisVector, Pi.smul_apply, smul_eq_mul] using hh
  have hone : c 0 = 1 := by
    have h := mul_left_cancel₀ hc0 (show c 0 * 1 = c 0 * c 0 by simpa using he)
    exact h.symm
  have hfix (i : Fin 6) : g.val (offDiagonalVector i) = offDiagonalVector i := by
    rw [hscale, hone, one_smul]
  have hp3 : mul (offDiagonalVector (F := F) 0) (offDiagonalVector 5) =
      -(basisVector 3 : Carrier F) := by
    funext i
    fin_cases i <;> simp [mul, offDiagonalVector, offDiagonalIndex, basisVector]
  have hp4 : mul (offDiagonalVector (F := F) 5) (offDiagonalVector 0) =
      -(basisVector 4 : Carrier F) := by
    funext i
    fin_cases i <;> simp [mul, offDiagonalVector, offDiagonalIndex, basisVector]
  have hf3 : g.val (basisVector 3) = basisVector 3 := by
    have h := automorphism_mul g (offDiagonalVector 0) (offDiagonalVector 5)
    rw [hp3, map_neg, hfix, hfix, hp3] at h
    exact neg_injective h
  have hf4 : g.val (basisVector 4) = basisVector 4 := by
    have h := automorphism_mul g (offDiagonalVector 5) (offDiagonalVector 0)
    rw [hp4, map_neg, hfix, hfix, hp4] at h
    exact neg_injective h
  have hb (i : Fin 8) : g.val (basisVector i) = basisVector i := by
    fin_cases i
    · exact hfix 0
    · exact hfix 1
    · exact hfix 2
    · exact hf3
    · exact hf4
    · exact hfix 3
    · exact hfix 4
    · exact hfix 5
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact (Pi.basisFun F (Fin 8)).ext (fun i => by
    simpa [Pi.basisFun_apply, basisVector] using hb i)

instance singularPointsFaithful : FaithfulSMul (Model F) (SingularPoints F) :=
  faithfulSMul_iff.mpr (singular_lines_kernel_trivial)

end Atlas.G2
