/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/LeechPlaneComplement.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.LeechOrthogonalComplement
public import Theory.AtlasPort.OtherSporadic.Conway.LeechTriangleSlice

/-!
The rank-22 integral complement of two independent Leech vectors.
The Gram determinant proves the rank calculation and faithfulness of the induced triangle-stabilizer representation.

Source: Gerald Höhn, `Atlas/Conway/LeechPlaneComplement.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def leechPlaneGramDet (v w : leech) : ℤ :=
  integerDot v.val v.val * integerDot w.val w.val - integerDot v.val w.val ^ 2

/-- The integral orthogonal complement of two actual Leech vectors. -/
def leechPlaneComplement (v w : leech) : Submodule ℤ leech :=
  leechOrthogonalComplement v ⊓ leechOrthogonalComplement w

def leechPlaneRestrictedFunctional (v w : leech) : leechOrthogonalComplement v →ₗ[ℤ] ℤ :=
  (leechVectorFunctional w).comp (leechOrthogonalComplement v).subtype

def leechPlaneKernelEquiv (v w : leech) :
    (leechPlaneRestrictedFunctional v w).ker ≃ₗ[ℤ] leechPlaneComplement v w where
  toFun z := ⟨z.val.val,z.val.prop,z.prop⟩
  invFun z := ⟨⟨z.val,z.prop.1⟩,z.prop.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem leechPlaneComplement_rank (v w : leech)
    (hv : integerDot v.val v.val ≠ 0) (hd : leechPlaneGramDet v w ≠ 0) :
    Module.finrank ℤ (leechPlaneComplement v w) = 22 := by
  let f := leechVectorFunctional v
  let q := leechVectorFunctional w
  let z := f v • w - f w • v
  have hz : z ∈ leechOrthogonalComplement v := by
    change f (f v • w - f w • v) = 0
    rw [map_sub,map_smul,map_smul]
    change f v*f w - f w*f v = 0
    ring
  let r := leechPlaneRestrictedFunctional v w
  have hq : r ⟨z,hz⟩ = leechPlaneGramDet v w := by
    change q (f v • w - f w • v) = _
    rw [map_sub,map_smul,map_smul]
    change integerDot v.val v.val * integerDot w.val w.val -
      integerDot v.val w.val * integerDot w.val v.val = _
    rw [integerDot_comm w.val v.val]
    simp [leechPlaneGramDet,pow_two]
  have hn : r.range ≠ ⊥ := by
    intro h
    have hh : r ⟨z,hz⟩ ∈ r.range := ⟨⟨z,hz⟩,rfl⟩
    rw [h,Submodule.mem_bot,hq] at hh
    exact hd hh
  have hlo : 1 ≤ Module.finrank ℤ r.range := Submodule.one_le_finrank_iff.mpr hn
  have hhi := LinearMap.finrank_le_finrank_of_injective r.range.subtype_injective
  have hr : Module.finrank ℤ r.range = 1 := by
    simp only [Module.finrank_self] at hhi
    omega
  have he := r.ker.finrank_quotient_add_finrank
  rw [r.quotKerEquivRange.finrank_eq,hr,leechOrthogonalComplement_rank v hv] at he
  rw [← (leechPlaneKernelEquiv v w).finrank_eq]
  change Module.finrank ℤ r.ker = 22
  omega

def leechPlaneComplementEquiv (v w : leech) (g : LeechTriangleStabilizer v w) :
    leechPlaneComplement v w ≃ₗ[ℤ] leechPlaneComplement v w where
  toFun z := ⟨g.val.val.val z.val,by
    constructor
    · have h := g.val.val.prop v z.val
      rw [show g.val.val.val v = v from g.val.prop] at h
      exact h.trans z.prop.1
    · have h := g.val.val.prop w z.val
      rw [show g.val.val.val w = w from g.prop] at h
      exact h.trans z.prop.2⟩
  invFun z := ⟨g⁻¹.val.val.val z.val,by
    constructor
    · have h := g⁻¹.val.val.prop v z.val
      rw [show g⁻¹.val.val.val v = v from g⁻¹.val.prop] at h
      exact h.trans z.prop.1
    · have h := g⁻¹.val.val.prop w z.val
      rw [show g⁻¹.val.val.val w = w from g⁻¹.prop] at h
      exact h.trans z.prop.2⟩
  left_inv z := Subtype.ext (g.val.val.val.symm_apply_apply z.val)
  right_inv z := Subtype.ext (g.val.val.val.apply_symm_apply z.val)
  map_add' z t := Subtype.ext (g.val.val.val.map_add z.val t.val)
  map_smul' r z := Subtype.ext (g.val.val.val.map_smul r z.val)

def leechPlaneRepresentation (v w : leech) : LeechTriangleStabilizer v w →*
    (leechPlaneComplement v w ≃ₗ[ℤ] leechPlaneComplement v w) where
  toFun := leechPlaneComplementEquiv v w
  map_one' := by apply LinearEquiv.ext; intro z; rfl
  map_mul' _ _ := by apply LinearEquiv.ext; intro z; rfl

theorem leechPlaneRepresentation_fixes_eq_one (v w : leech)
    (hd : leechPlaneGramDet v w ≠ 0) (g : LeechTriangleStabilizer v w)
    (hg : ∀ z : leechPlaneComplement v w, leechPlaneRepresentation v w g z = z) : g = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  let f := leechVectorFunctional v
  let q := leechVectorFunctional w
  let D := leechPlaneGramDet v w
  let A := q w*f z - f w*q z
  let B := f v*q z - f w*f z
  let u := D • z - A • v - B • w
  have hfv : f w = q v := integerDot_comm _ _
  have hD : D = f v*q w - f w*f w := by simp [D,leechPlaneGramDet,f,q,leechVectorFunctional,pow_two]
  have hu : u ∈ leechPlaneComplement v w := by
    constructor
    · change f (D • z - A • v - B • w) = 0
      rw [map_sub,map_sub,map_smul,map_smul,map_smul]
      change D*f z - A*f v - B*f w = 0
      dsimp [A,B]
      rw [hD]
      ring
    · change q (D • z - A • v - B • w) = 0
      rw [map_sub,map_sub,map_smul,map_smul,map_smul]
      change D*q z - A*q v - B*q w = 0
      dsimp [A,B]
      rw [hD,← hfv]
      ring
  have he := congrArg (fun y : leechPlaneComplement v w => y.val) (hg ⟨u,hu⟩)
  change g.val.val.val u = u at he
  dsimp [u] at he
  rw [map_sub,map_sub,map_smul,map_smul,map_smul,
    show g.val.val.val v = v from g.val.prop,
    show g.val.val.val w = w from g.prop] at he
  have he' : D • g.val.val.val z = D • z := sub_left_injective (sub_left_injective he)
  apply Subtype.ext
  funext i
  have hi := congrArg (fun y : leech => y.val i) he'
  change D*(g.val.val.val z).val i = D*z.val i at hi
  exact mul_left_cancel₀ hd hi

theorem leechPlaneRepresentation_injective (v w : leech)
    (hd : leechPlaneGramDet v w ≠ 0) : Function.Injective (leechPlaneRepresentation v w) := by
  intro g h he
  have hk : leechPlaneRepresentation v w (g⁻¹*h) = 1 := by
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hh : g⁻¹*h = 1 := leechPlaneRepresentation_fixes_eq_one v w hd _ (by
    intro z
    exact congrArg (fun e : leechPlaneComplement v w ≃ₗ[ℤ] leechPlaneComplement v w => e z) hk)
  exact inv_mul_eq_one.mp hh

theorem leechPlaneRepresentation_preserves (v w : leech) (g : LeechTriangleStabilizer v w)
    (z t : leechPlaneComplement v w) :
    integerDot (leechPlaneRepresentation v w g z).val.val
      (leechPlaneRepresentation v w g t).val.val = integerDot z.val.val t.val.val :=
  g.val.val.prop z.val t.val
end Atlas.Conway
