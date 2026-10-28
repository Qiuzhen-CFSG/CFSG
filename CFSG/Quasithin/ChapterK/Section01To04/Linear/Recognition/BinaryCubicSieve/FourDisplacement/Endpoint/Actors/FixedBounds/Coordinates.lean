module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.StandardModel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.CharP.Two

/-!
# Fourteen coordinates on the literal adjoint quotient

Subtract the bottom-right scalar entry, then retain the twelve off-diagonal
entries and the first two diagonal entries. Trace zero determines the third
diagonal entry. The inverse constructs the unique trace-zero representative
with bottom-right entry zero. Both inverse identities are proved through the
actual quotient map, so scalar displacement of representatives is retained.

Source: Guralnick–Malle, Classification of 2F-modules II, Lemma 4.5 and
Proposition 4.8 step 3A; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Representation Representation.BinaryOffender Matrix
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
abbrev Coordinates := Fin 14 → ZMod 2

def pack : ActorMatrix →ₗ[ZMod 2] Coordinates where
  toFun X := ![X 0 1, X 0 2, X 0 3, X 1 0, X 1 2, X 1 3,
    X 2 0, X 2 1, X 2 3, X 3 0, X 3 1, X 3 2, X 0 0 + X 3 3, X 1 1 + X 3 3]
  map_add' X Y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c X := by ext i; fin_cases i <;> simp [mul_add]

def unpack : Coordinates →ₗ[ZMod 2] ActorMatrix where
  toFun v := !![v 12, v 0, v 1, v 2; v 3, v 13, v 4, v 5;
    v 6, v 7, v 12 + v 13, v 8; v 9, v 10, v 11, 0]
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring
  map_smul' c v := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_add]

@[simp] theorem pack_unpack (v : Coordinates) : pack (unpack v) = v := by
  ext i; fin_cases i <;> simp [pack, unpack]

@[simp] theorem trace_unpack (v : Coordinates) : (unpack v).trace = 0 := by
  simp [unpack, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
  ring_nf
  simp [CharTwo.two_eq_zero]

@[simp] theorem pack_one : pack (1 : ActorMatrix) = 0 := by
  decide

theorem unpack_pack (X : ActorMatrix) (h : X.trace = 0) :
    unpack (pack X) = X + X 3 3 • (1 : ActorMatrix) := by
  have hdiag : X 0 0 + X 1 1 + X 2 2 + X 3 3 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_succ, add_assoc] using h
  have h22 : X 0 0 + X 1 1 = X 2 2 + X 3 3 := by
    have he := congrArg (fun z => z + (X 2 2 + X 3 3)) hdiag
    simpa only [add_assoc, add_left_comm, add_comm, CharTwo.add_self_eq_zero, add_zero, zero_add] using he
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unpack, pack]
  · ring_nf
    simpa [CharTwo.two_eq_zero, add_comm] using h22
  · exact (CharTwo.add_self_eq_zero _).symm

noncomputable def unpackTrace : Coordinates →ₗ[ZMod 2] TraceZero :=
  (Matrix.toLin'.toLinearMap.comp unpack).codRestrict _ (fun v => by
    change LinearMap.trace (ZMod 2) Natural (Matrix.toLin' (unpack v)) = 0
    rw [Matrix.trace_toLin'_eq, trace_unpack])

noncomputable def packTrace : TraceZero →ₗ[ZMod 2] Coordinates :=
  pack.comp (LinearMap.toMatrix'.toLinearMap.comp (LinearMap.ker (LinearMap.trace (ZMod 2) Natural)).subtype)

@[simp] theorem packTrace_scalarVector : packTrace scalarVector = 0 := by
  change pack (LinearMap.toMatrix' LinearMap.id) = 0
  simp

noncomputable def quotientCoordinates : Adjoint →ₗ[ZMod 2] Coordinates :=
  scalarLine.toSubmodule.liftQ packTrace (by
    intro f hf
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
    change packTrace (c • scalarVector) = 0
    simp)

@[simp] theorem quotientCoordinates_mk (f : TraceZero) :
    quotientCoordinates (mkAdjoint f) = pack (LinearMap.toMatrix' f.val) := rfl

@[simp] theorem quotientCoordinates_unpackTrace (v : Coordinates) :
    quotientCoordinates (mkAdjoint (unpackTrace v)) = v := by
  rw [quotientCoordinates_mk]
  change pack (LinearMap.toMatrix' (Matrix.toLin' (unpack v))) = v
  rw [LinearMap.toMatrix'_toLin', pack_unpack]

theorem mk_unpackTrace_packTrace (f : TraceZero) :
    mkAdjoint (unpackTrace (packTrace f)) = mkAdjoint f := by
  have ht : (LinearMap.toMatrix' f.val).trace = 0 := by
    have hf := f.property
    change LinearMap.trace (ZMod 2) Natural f.val = 0 at hf
    rwa [LinearMap.trace_eq_matrix_trace (ZMod 2) (Pi.basisFun (ZMod 2) (Fin 4)),
      LinearMap.toMatrix_eq_toMatrix'] at hf
  have he : unpackTrace (packTrace f) = f + (LinearMap.toMatrix' f.val) 3 3 • scalarVector := by
    apply Subtype.ext
    apply LinearMap.toMatrix'.injective
    change LinearMap.toMatrix' (Matrix.toLin' (unpack (pack (LinearMap.toMatrix' f.val)))) = _
    rw [LinearMap.toMatrix'_toLin', unpack_pack _ ht]
    simp [scalarVector]
  rw [he, map_add, map_smul]
  have hs : mkAdjoint scalarVector = 0 := (mkAdjoint_eq_zero_iff _).mpr ⟨1, one_smul _ _⟩
  simp [hs]

noncomputable def coordinateEquiv : Adjoint ≃ₗ[ZMod 2] Coordinates :=
  { quotientCoordinates with
    invFun := fun v => mkAdjoint (unpackTrace v)
    left_inv := by
      intro v
      obtain ⟨f, rfl⟩ := mkAdjoint_surjective v
      exact mk_unpackTrace_packTrace f
    right_inv := quotientCoordinates_unpackTrace }

@[simp] theorem coordinateEquiv_mk (f : TraceZero) :
    coordinateEquiv (mkAdjoint f) = pack (LinearMap.toMatrix' f.val) := rfl

@[simp] theorem coordinateEquiv_symm (v : Coordinates) :
    coordinateEquiv.symm v = mkAdjoint (unpackTrace v) := rfl


end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
