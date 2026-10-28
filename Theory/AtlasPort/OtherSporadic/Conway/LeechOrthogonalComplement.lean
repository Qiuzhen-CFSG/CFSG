/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/LeechOrthogonalComplement.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MinimumVectorStabilizer
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechRank
public import Mathlib.LinearAlgebra.Dimension.RankNullity
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/LeechOrthogonalComplement.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators

/-- Integral pairing functional on the retained Golay Leech lattice. -/
def leechVectorFunctional (v : leech) : leech →ₗ[ℤ] ℤ where
  toFun x := integerDot v.val x.val
  map_add' x y := integerDot_add_right _ _ _
  map_smul' r x := by
    change integerDot v.val (r • x.val) = r * integerDot v.val x.val
    simp only [integerDot,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The integral orthogonal complement, as a sublattice of the actual Leech lattice. -/
def leechOrthogonalComplement (v : leech) : Submodule ℤ leech :=
  (leechVectorFunctional v).ker

theorem leechOrthogonalComplement_rank (v : leech)
    (hv : integerDot v.val v.val ≠ 0) : Module.finrank ℤ (leechOrthogonalComplement v) = 23 := by
  let f := leechVectorFunctional v
  have hn : f.range ≠ ⊥ := by
    intro h
    have hh : f v ∈ f.range := ⟨v,rfl⟩
    rw [h] at hh
    exact hv hh
  have hlo : 1 ≤ Module.finrank ℤ f.range := Submodule.one_le_finrank_iff.mpr hn
  have hhi := LinearMap.finrank_le_finrank_of_injective f.range.subtype_injective
  have hr : Module.finrank ℤ f.range = 1 := by
    simp only [Module.finrank_self] at hhi
    omega
  have he := f.ker.finrank_quotient_add_finrank
  rw [f.quotKerEquivRange.finrank_eq,hr,leech_rank] at he
  change Module.finrank ℤ f.ker = 23
  omega

/-- Restrict an actual vector stabilizer element to the integral complement. -/
def leechComplementEquiv (v : leech) (g : fullVectorStabilizer v) :
    leechOrthogonalComplement v ≃ₗ[ℤ] leechOrthogonalComplement v where
  toFun x := ⟨g.val.val x.val,by
    have h := g.val.prop v x.val
    rw [show g.val.val v = v from g.prop] at h
    exact h.trans x.prop⟩
  invFun x := ⟨g.val.val.symm x.val,by
    have h := g⁻¹.val.prop v x.val
    rw [show g⁻¹.val.val v = v from g⁻¹.prop] at h
    exact h.trans x.prop⟩
  left_inv x := Subtype.ext (g.val.val.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.val.val.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (g.val.val.map_add x.val y.val)
  map_smul' r x := Subtype.ext (g.val.val.map_smul r x.val)

def leechComplementRepresentation (v : leech) :
    fullVectorStabilizer v →* (leechOrthogonalComplement v ≃ₗ[ℤ] leechOrthogonalComplement v) where
  toFun := leechComplementEquiv v
  map_one' := by apply LinearEquiv.ext; intro x; rfl
  map_mul' g h := by apply LinearEquiv.ext; intro x; rfl

theorem leechComplement_fixes_eq_one (v : leech) (hv : integerDot v.val v.val ≠ 0)
    (g : fullVectorStabilizer v)
    (hg : ∀ x : leechOrthogonalComplement v, leechComplementEquiv v g x = x) : g = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  let f := leechVectorFunctional v
  let w := f v • x - f x • v
  have hw : w ∈ leechOrthogonalComplement v := by
    change f (f v • x - f x • v) = 0
    rw [map_sub,map_smul,map_smul]
    change f v * f x - f x * f v = 0
    ring
  have he := congrArg (fun y : leechOrthogonalComplement v => y.val) (hg ⟨w,hw⟩)
  change g.val.val w = w at he
  dsimp [w] at he
  rw [map_sub,map_smul,map_smul,show g.val.val v = v from g.prop] at he
  have hh := congrArg (fun y : leech => y + f x • v) he
  simp only [sub_add_cancel] at hh
  apply Subtype.ext
  funext i
  have hi := congrArg (fun y : leech => y.val i) hh
  change f v * (g.val.val x).val i = f v * x.val i at hi
  exact mul_left_cancel₀ hv hi

theorem leechComplementRepresentation_injective (v : leech)
    (hv : integerDot v.val v.val ≠ 0) : Function.Injective (leechComplementRepresentation v) := by
  intro g h he
  have hk : leechComplementRepresentation v (g⁻¹*h) = 1 := by
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hh : g⁻¹*h = 1 := leechComplement_fixes_eq_one v hv _ (by
    intro x
    exact congrArg (fun e : leechOrthogonalComplement v ≃ₗ[ℤ] leechOrthogonalComplement v => e x) hk)
  exact inv_mul_eq_one.mp hh

theorem leechComplementRepresentation_preserves (v : leech) (g : fullVectorStabilizer v)
    (x y : leechOrthogonalComplement v) :
    integerDot ((leechComplementRepresentation v g x).val.val)
      ((leechComplementRepresentation v g y).val.val) = integerDot x.val.val y.val.val :=
  g.val.prop x.val y.val

end Atlas.Conway
