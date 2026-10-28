module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.Model
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# A characteristic-independent SL3 block representation

Full matrix conjugation, nine natural triples, nine dual triples and fifteen
fixed coordinates form a genuine 78-dimensional representation of the full
SL3 matrix group. The signed elementary formulas keep their original
parameters; the dual action uses inverse transpose.

Using all matrices retains the scalar direction in characteristic three.
The separate `Coordinates` module specifies the comparison with the E6
Geck lattice. This module proves the representation and its generator formulas,
not the E6 comparison. The consumer `ShortA2.E6Model` transports this action
and restricts its range using elementary generation.

Source: the common-lattice subsystem construction of GLS3 §2.6.2, used in
Aschbacher--Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2.E6Model
open Matrix

/-- Matrix entries, nine natural and nine dual triples, and fifteen fixed coordinates. -/
abbrev BlockIndex := (Fin 3 × Fin 3) ⊕ (Bool × Fin 9 × Fin 3) ⊕ Fin 15
abbrev BlockSpace (R : Type*) := BlockIndex → R

variable (R : Type*) [CommRing R]

def matrixPart (v : BlockSpace R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => v (.inl (i, j))
def triplePart (v : BlockSpace R) (s : Bool) (h : Fin 9) : Fin 3 → R :=
  fun i => v (.inr (.inl (s, h, i)))

variable (F : Type*) [Field F]

/-- Conjugation on all matrices, the natural and contragredient actions, and the identity. -/
def blockLinear (g : Model F) : BlockSpace F →ₗ[F] BlockSpace F where
  toFun v c := match c with
    | .inl (i, j) => (g.val * matrixPart F v * g⁻¹.val) i j
    | .inr (.inl (true, h, i)) => (g.val *ᵥ triplePart F v true h) i
    | .inr (.inl (false, h, i)) => (g⁻¹.val.transpose *ᵥ triplePart F v false h) i
    | .inr (.inr i) => v (.inr (.inr i))
  map_add' v w := by
    funext c
    rcases c with ⟨i,j⟩ | (⟨s,h,i⟩ | i)
    · change (g.val * (matrixPart F v + matrixPart F w) * g⁻¹.val) i j = _
      simp only [mul_add, add_mul, Matrix.add_apply, Pi.add_apply]
    · cases s <;>
        change (_ *ᵥ (triplePart F v _ h + triplePart F w _ h)) i = _ <;>
        simp only [Matrix.mulVec_add, Pi.add_apply]
    · rfl
  map_smul' t v := by
    funext c
    rcases c with ⟨i,j⟩ | (⟨s,h,i⟩ | i)
    · change (g.val * (t • matrixPart F v) * g⁻¹.val) i j = _
      simp only [mul_smul_comm, smul_mul_assoc, Matrix.smul_apply, smul_eq_mul,
        RingHom.id_apply, Pi.smul_apply]
    · cases s <;>
        change (_ *ᵥ (t • triplePart F v _ h)) i = _ <;>
        simp only [Matrix.mulVec_smul, Pi.smul_apply, RingHom.id_apply]
    · rfl

@[simp] theorem matrixPart_blockLinear (g : Model F) (v : BlockSpace F) :
    matrixPart F (blockLinear F g v) = g.val * matrixPart F v * g⁻¹.val := rfl
@[simp] theorem triplePart_blockLinear_true (g : Model F) (v : BlockSpace F) (h : Fin 9) :
    triplePart F (blockLinear F g v) true h = g.val *ᵥ triplePart F v true h := rfl
@[simp] theorem triplePart_blockLinear_false (g : Model F) (v : BlockSpace F) (h : Fin 9) :
    triplePart F (blockLinear F g v) false h =
      g⁻¹.val.transpose *ᵥ triplePart F v false h := rfl

theorem blockLinear_one : blockLinear F 1 = LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext c
  rcases c with ⟨i,j⟩ | (⟨s,h,i⟩ | i)
  · simp [blockLinear, matrixPart]
  · cases s <;> change (_ *ᵥ triplePart F v _ h) i = _ <;>
      simp [triplePart]
  · rfl

theorem blockLinear_mul (g h : Model F) :
    blockLinear F (g * h) = (blockLinear F g).comp (blockLinear F h) := by
  apply LinearMap.ext
  intro v
  funext c
  rcases c with ⟨i,j⟩ | (⟨s,a,i⟩ | i)
  · change ((g*h).val * matrixPart F v * (g*h)⁻¹.val) i j =
      (g.val * matrixPart F (blockLinear F h v) * g⁻¹.val) i j
    rw [matrixPart_blockLinear, _root_.mul_inv_rev]
    change ((g.val * h.val) * matrixPart F v * (h⁻¹.val * g⁻¹.val)) i j = _
    simp only [mul_assoc]
  · cases s
    · change ((g*h)⁻¹.val.transpose *ᵥ triplePart F v false a) i =
        (g⁻¹.val.transpose *ᵥ triplePart F (blockLinear F h v) false a) i
      rw [triplePart_blockLinear_false, _root_.mul_inv_rev]
      change ((h⁻¹.val * g⁻¹.val).transpose *ᵥ triplePart F v false a) i = _
      rw [Matrix.transpose_mul, Matrix.mulVec_mulVec]
    · change ((g*h).val *ᵥ triplePart F v true a) i =
        (g.val *ᵥ triplePart F (blockLinear F h v) true a) i
      rw [triplePart_blockLinear_true]
      change ((g.val * h.val) *ᵥ triplePart F v true a) i = _
      rw [Matrix.mulVec_mulVec]
  · rfl

/-- A genuine representation of full SL3; no irreducible summand is selected. -/
def blockAction : Model F →* (BlockSpace F ≃ₗ[F] BlockSpace F) where
  toFun g := LinearEquiv.ofLinearMap (blockLinear F g) (blockLinear F g⁻¹)
    (by rw [← blockLinear_mul, mul_inv_cancel, blockLinear_one])
    (by rw [← blockLinear_mul, inv_mul_cancel, blockLinear_one])
  map_one' := LinearEquiv.toLinearMap_injective (blockLinear_one F)
  map_mul' g h := LinearEquiv.toLinearMap_injective (blockLinear_mul F g h)

@[simp] theorem blockAction_apply (g : Model F) (v : BlockSpace F) :
    blockAction F g v = blockLinear F g v := rfl

/-- Row and column for the shared signed elementary marking. -/
def generatorRow (s k : Bool) : Fin 3 :=
  if k then (if s then 0 else 1) else (if s then 1 else 2)
def generatorColumn (s k : Bool) : Fin 3 := generatorRow (!s) k

theorem modelGenerator_matrix (s k : Bool) (t : F) :
    (modelGenerator F s k t).val =
      1 + Matrix.single (generatorRow s k) (generatorColumn s k) t := by
  cases s <;> cases k <;> rfl

theorem modelGenerator_inv_matrix (s k : Bool) (t : F) :
    (modelGenerator F s k t)⁻¹.val =
      1 + Matrix.single (generatorRow s k) (generatorColumn s k) (-t) := by
  cases s <;> cases k <;>
    simp only [modelGenerator, Bool.false_eq_true, if_false, if_true,
      SpecialLinearGroup.transvection_inv] <;> rfl

/-- The full matrix block is acted on by conjugation, including its scalar line. -/
theorem blockAction_generator_matrix (s k : Bool) (t : F) (v : BlockSpace F) :
    matrixPart F (blockAction F (modelGenerator F s k t) v) =
      (1 + Matrix.single (generatorRow s k) (generatorColumn s k) t) *
        matrixPart F v *
          (1 + Matrix.single (generatorRow s k) (generatorColumn s k) (-t)) := by
  rw [blockAction_apply, matrixPart_blockLinear,
    modelGenerator_matrix, modelGenerator_inv_matrix]

theorem blockAction_generator_natural (s k : Bool) (t : F) (v : BlockSpace F) (h : Fin 9) :
    triplePart F (blockAction F (modelGenerator F s k t) v) true h =
      (1 + Matrix.single (generatorRow s k) (generatorColumn s k) t) *ᵥ
        triplePart F v true h := by
  rw [blockAction_apply, triplePart_blockLinear_true, modelGenerator_matrix]

theorem blockAction_generator_dual (s k : Bool) (t : F) (v : BlockSpace F) (h : Fin 9) :
    triplePart F (blockAction F (modelGenerator F s k t) v) false h =
      (1 + Matrix.single (generatorRow s k) (generatorColumn s k) (-t)).transpose *ᵥ
        triplePart F v false h := by
  rw [blockAction_apply, triplePart_blockLinear_false, modelGenerator_inv_matrix]

@[simp] theorem blockAction_fixed (g : Model F) (v : BlockSpace F) (i : Fin 15) :
    blockAction F g v (.inr (.inr i)) = v (.inr (.inr i)) := rfl

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2.E6Model
