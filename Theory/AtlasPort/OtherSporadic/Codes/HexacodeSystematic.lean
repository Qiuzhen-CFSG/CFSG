/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.MonomialIsometries
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeCounting
public import Theory.AtlasPort.OtherSporadic.Codes.BinaryLift

/-!
# A systematic encoder for the hexacode

The hexacode is parametrized by its first three coordinates using local
Kleinian isometries. Coordinate identities prove the encoder is linear and
supply the systematic presentation used in subsequent normal-form arguments.

Source: `Atlas/Codes/HexacodeSystematic.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes
set_option maxHeartbeats 1000000

/-- Ordered positions transported through the existing index equivalence. -/
def hexPos (i : Fin 6) : HexIndex := hexIndexEquiv.symm i

theorem hexPos_order : hexPos = ![(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)] := by
  funext i; revert i; decide

@[simp] theorem hexPos_index (i : HexIndex) : hexPos (hexIndexEquiv i) = i :=
  hexIndexEquiv.symm_apply_apply i
@[simp] theorem index_hexPos (i : Fin 6) : hexIndexEquiv (hexPos i) = i :=
  hexIndexEquiv.apply_symm_apply i

def firstThree : Fin 3 ↪ HexIndex where
  toFun i := hexPos (Fin.castAdd 3 i)
  inj' := by
    intro i j h
    have hh := hexIndexEquiv.symm.injective h
    exact Fin.ext (congrArg (fun k : Fin 6 => k.val) hh)

def systematicEncoder : (Fin 3 → K) →ₗ[Bit] HexWord where
  toFun x i := ![x 0,x 1,x 2,
    localU (x 0)+x 1+localU (x 2),
    localKappa⁻¹ (x 0)+localV (x 1)+x 2,
    localW (x 0)+localKappa (x 1)+localU (x 2)] (hexIndexEquiv i)
  map_add' := by
    intro x y; funext i
    dsimp only [Pi.add_apply]
    generalize hexIndexEquiv i = k
    fin_cases k <;>
      simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', map_add]
    all_goals abel
  map_smul' := by
    intro r x; funext i
    dsimp only [Pi.smul_apply]
    generalize hexIndexEquiv i = k
    fin_cases k <;>
      simp only [Matrix.cons_val_zero', Matrix.cons_val_succ',
        map_smul, smul_add, RingHom.id_apply]

@[simp] theorem systematic_pos0 (x : Fin 3 → K) :
    systematicEncoder x (hexPos 0) = x 0 := rfl

@[simp] theorem systematic_pos1 (x : Fin 3 → K) :
    systematicEncoder x (hexPos 1) = x 1 := rfl

@[simp] theorem systematic_pos2 (x : Fin 3 → K) :
    systematicEncoder x (hexPos 2) = x 2 := rfl

@[simp] theorem systematic_pos3 (x : Fin 3 → K) :
    systematicEncoder x (hexPos 3) = localU (x 0) + x 1 + localU (x 2) := rfl

@[simp] theorem systematic_pos4 (x : Fin 3 → K) :
    systematicEncoder x (hexPos 4) = localKappa⁻¹ (x 0) + localV (x 1) + x 2 := rfl

@[simp] theorem systematic_pos5 (x : Fin 3 → K) :
    systematicEncoder x (hexPos 5) = localW (x 0) + localKappa (x 1) + localU (x 2) := rfl

theorem systematic_on_basis : ∀ k : Fin 6,
    systematicEncoder (fun i => hexGenerators k (firstThree i)) = hexGenerators k := by
  decide

theorem systematic_reconstruct (w : hexacode) :
    systematicEncoder (hexProjection firstThree w) = w.val := by
  have h : systematicEncoder.comp (hexProjection firstThree) = hexacode.subtype := by
    apply hexBasis.ext
    intro k
    change systematicEncoder (fun i => (hexBasis k : HexWord) (firstThree i)) = (hexBasis k : HexWord)
    rw [hexBasis_coe]
    exact systematic_on_basis k
  exact LinearMap.congr_fun h w

theorem systematic_mem (x : Fin 3 → K) : systematicEncoder x ∈ hexacode := by
  obtain ⟨w, hw⟩ := (hexProjection_bijective firstThree).2 x
  rw [← hw, systematic_reconstruct]
  exact w.prop

theorem hexacode_systematic (w : HexWord) : w ∈ hexacode ↔
    w (hexPos 3) = localU (w (hexPos 0)) + w (hexPos 1) + localU (w (hexPos 2)) ∧
    w (hexPos 4) = localKappa⁻¹ (w (hexPos 0)) + localV (w (hexPos 1)) + w (hexPos 2) ∧
    w (hexPos 5) = localW (w (hexPos 0)) + localKappa (w (hexPos 1)) + localU (w (hexPos 2)) := by
  constructor
  · intro hw
    have h := systematic_reconstruct ⟨w,hw⟩
    exact ⟨(congrFun h (hexPos 3)).symm, (congrFun h (hexPos 4)).symm,
      (congrFun h (hexPos 5)).symm⟩
  · rintro ⟨h3,h4,h5⟩
    have hh : systematicEncoder (fun i => w (firstThree i)) = w := by
      funext i
      obtain ⟨k,rfl⟩ := hexIndexEquiv.symm.surjective i
      fin_cases k
      · rfl
      · rfl
      · rfl
      · exact h3.symm
      · exact h4.symm
      · exact h5.symm
    rw [← hh]
    exact systematic_mem _

abbrev HexAutomorphisms := Monomial.stabilizer hexacode

def hexCoordinateHom : HexAutomorphisms →* Equiv.Perm HexIndex :=
  Monomial.coordinateHom.comp (Monomial.stabilizer hexacode).subtype

def hexAction : HexAutomorphisms →* (hexacode ≃ₗ[Bit] hexacode) :=
  Monomial.restriction hexacode

end Atlas.Codes
