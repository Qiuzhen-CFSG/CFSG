/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/SextetSignConjugation.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.TetradConjugation
public import Theory.AtlasPort.OtherSporadic.Conway.SextetIsometry
/-!
Explicit sextet and tetrad isometries of the integral Leech lattice.
Coordinate identities and the retained lattice generators certify the isometry operations.

Source: Gerald Höhn, `Atlas/Conway/SextetSignConjugation.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def rationalSignChange (c : BinaryWord) : RationalCoordinates →ₗ[ℚ] RationalCoordinates where
  toFun x := fun i => if c i = 0 then x i else -x i
  map_add' _ _ := by ext i; by_cases hc : c i = 0 <;> simp [hc,add_comm]
  map_smul' _ _ := by ext i; by_cases hc : c i = 0 <;> simp [hc]

theorem rationalEmbedding_signChange (c : BinaryWord) (x : IntegerCoordinates) :
    rationalEmbedding (signChange c x) = rationalSignChange c (rationalEmbedding x) := by
  funext i
  simp [rationalEmbedding,signChange,rationalSignChange]

theorem sextet_sign_conjugation_coordinate (h : HexWord) (x : RationalCoordinates)
    (i : HexIndex) (k : Tetrad) :
    sextetReflection (rationalSignChange (jWord h) (sextetReflection x)) (i,k) =
      conjugatedSign (h i) k * x (i,tetradSwitch (h i) k) := by
  let v : Tetrad → ℚ := fun l => x (i,l)
  let w := (tetradDiagonal (h i)).mulVec (tetradReflectionMatrix.mulVec v)
  have hw (l : Tetrad) : rationalSignChange (jWord h) (sextetReflection x) (i,l) =
      sextetBlockSign i * w l := by
    change (if j (h i) l = 0 then sextetReflection x (i,l) else -sextetReflection x (i,l)) = _
    simp only [w,tetradDiagonal,Matrix.mulVec_diagonal,tetradReflectionMatrix_apply,
      sextetReflection_apply,v]
    split_ifs <;> ring
  calc
    _ = sextetBlockSign i * (sextetBlockSign i * w k -
        (∑ l, sextetBlockSign i * w l) / 2) := by
      rw [sextetReflection_apply]
      simp_rw [hw]
    _ = (sextetBlockSign i * sextetBlockSign i) * tetradReflectionMatrix.mulVec w k := by
      rw [tetradReflectionMatrix_apply,← Finset.mul_sum]
      ring
    _ = _ := by
      rw [sextetBlockSign_sq,one_mul]
      exact congrFun (tetrad_conjugation_apply (h i) v) k

def hexSwitch (h : HexWord) : Equiv.Perm Omega where
  toFun p := (p.1,tetradSwitch (h p.1) p.2)
  invFun p := (p.1,tetradSwitch (h p.1) p.2)
  left_inv p := Prod.ext rfl (tetradSwitch_involutive (h p.1) p.2)
  right_inv p := Prod.ext rfl (tetradSwitch_involutive (h p.1) p.2)

def hexConjugatedSignWord (h : HexWord) : BinaryWord :=
  fun p => if h p.1 = 0 then 0 else 1 - j (h p.1) p.2

theorem conjugatedSign_eq_sign : ∀ (u : K) (k : Tetrad),
    conjugatedSign u k = if (if u = 0 then (0 : Bit) else 1 - j u k) = 0 then 1 else -1 := by
  decide +kernel

theorem sextet_sign_conjugation (h : HexWord) (x : IntegerCoordinates) :
    sextetReflection (rationalSignChange (jWord h) (sextetReflection (rationalEmbedding x))) =
      rationalEmbedding (signChange (hexConjugatedSignWord h) (integerPermutation (hexSwitch h) x)) := by
  funext p
  rw [sextet_sign_conjugation_coordinate,conjugatedSign_eq_sign]
  change (if (if h p.1 = 0 then (0 : Bit) else 1 - j (h p.1) p.2) = 0 then 1 else -1) *
    (x (p.1,tetradSwitch (h p.1) p.2) : ℚ) = _
  simp only [rationalEmbedding,signChange,integerPermutation,hexSwitch,hexConjugatedSignWord,
    LinearMap.coe_mk,AddHom.coe_mk,LinearEquiv.coe_mk,Equiv.coe_fn_mk]
  split_ifs <;> simp

end Atlas.Conway
