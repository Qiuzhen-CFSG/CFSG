module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.Actions
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Tactic.FinCases

/-!
# Alternating forms for the parity-twisted binary action

The binary automorphism group acts on nondegenerate alternating forms by
inverse pullback. The form with matrix J+I is fixed by the twisted S₄.
More strongly, it is the only nondegenerate alternating form fixed by the
coordinate three-cycle (0 1 2). We prove uniqueness by recovering all six
upper-triangular coefficients and checking the finite binary possibilities
in the kernel. This replaces the longer calculation of all S₄-orbits.

This is the form-theoretic input to the concrete order-360 overgroup argument
used for Janko, “A characterization of the Mathieu simple groups, I”,
J. Algebra 9 (1968), Section 2, Lemma 6, p.6.
-/

@[expose] public section

open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open LinearMap Matrix
namespace Theory.GroupTheory.HeldM22A10.BinaryRecognition
abbrev V := Fin 4 → ZMod 2

def linear (g : MulAut BinaryFour) : V ≃ₗ[ZMod 2] V where
  toFun v := (g (Multiplicative.ofAdd v)).toAdd
  invFun v := (g.symm (Multiplicative.ofAdd v)).toAdd
  left_inv v := g.left_inv v
  right_inv v := g.right_inv v
  map_add' v w := g.map_mul v w
  map_smul' c v := by
    have hc : c = 0 ∨ c = 1 := by decide +revert
    rcases hc with rfl | rfl
    · simp
    · simp

abbrev Form := {B : LinearMap.BilinForm (ZMod 2) V // B.IsAlt ∧ B.Nondegenerate}

instance : Finite Form :=
  Finite.of_injective (fun B : Form => fun v w : V => B.val v w) (by
    intro B C h
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact congrFun (congrFun h v) w)

def act (g : MulAut BinaryFour) (B : Form) : Form :=
  ⟨B.val.comp (linear g).symm.toLinearMap (linear g).symm.toLinearMap,
    (fun v => B.property.1 _), by
      constructor
      · intro v hv
        have hz := B.property.2.1 ((linear g).symm v) (by
          intro w
          obtain ⟨w, rfl⟩ := (linear g).symm.surjective w
          exact hv w)
        exact (linear g).symm.injective (hz.trans (map_zero _).symm)
      · intro v hv
        have hz := B.property.2.2 ((linear g).symm v) (by
          intro w
          obtain ⟨w, rfl⟩ := (linear g).symm.surjective w
          exact hv w)
        exact (linear g).symm.injective (hz.trans (map_zero _).symm)⟩

instance : MulAction (MulAut BinaryFour) Form where
  smul := act
  one_smul B := by apply Subtype.ext; ext v w; rfl
  mul_smul g h B := by apply Subtype.ext; ext v w; rfl

def formMatrix (c : Fin 6 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, c 0, c 1, c 2; c 0, 0, c 3, c 4; c 1, c 3, 0, c 5; c 2, c 4, c 5, 0]

def standard : LinearMap.BilinForm (ZMod 2) V := (formMatrix (fun _ => 1)).toBilin'

set_option maxRecDepth 10000 in
 theorem standard_alt : standard.IsAlt := by
  change ∀ v, standard v v = 0
  decide +kernel

set_option maxRecDepth 10000 in
 theorem standard_nondegenerate : standard.Nondegenerate := by
  constructor
  · change ∀ v, (∀ w, standard v w = 0) → v = 0
    decide +kernel
  · change ∀ w, (∀ v, standard v w = 0) → w = 0
    decide +kernel

def base : Form := ⟨standard, standard_alt, standard_nondegenerate⟩

 theorem twisted_fixes : ∀ s : SymmetricFour, ∀ v w : V,
    standard ((twistedAction s) (Multiplicative.ofAdd v)).toAdd
      ((twistedAction s) (Multiplicative.ofAdd w)).toAdd = standard v w := by
  decide +kernel

def cycle : SymmetricFour := Equiv.swap 0 1 * Equiv.swap 1 2

def coordinates (B : LinearMap.BilinForm (ZMod 2) V) : Fin 6 → ZMod 2 :=
  ![B.toMatrix' 0 1, B.toMatrix' 0 2, B.toMatrix' 0 3,
    B.toMatrix' 1 2, B.toMatrix' 1 3, B.toMatrix' 2 3]

theorem matrix_coordinates (B : Form) : B.val.toMatrix' = formMatrix (coordinates B.val) := by
  have hd (i : Fin 4) : B.val.toMatrix' i i = 0 := B.property.1 _
  have hs (i j : Fin 4) : B.val.toMatrix' i j = B.val.toMatrix' j i := by
    change B.val (Pi.single i 1) (Pi.single j 1) = B.val (Pi.single j 1) (Pi.single i 1)
    simpa only [CharTwo.neg_eq] using B.property.1.neg_eq (Pi.single i 1) (Pi.single j 1)
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp [formMatrix, coordinates] <;>
    first | rfl | exact hd _ | exact hs _ _

set_option maxRecDepth 10000 in
 theorem fixed_coordinates : ∀ c : Fin 6 → ZMod 2,
    (∀ v w : V, (formMatrix c).toBilin'
      ((twistedAction cycle) (Multiplicative.ofAdd v)).toAdd
      ((twistedAction cycle) (Multiplicative.ofAdd w)).toAdd = (formMatrix c).toBilin' v w) →
    (∀ v : V, (∀ w : V, (formMatrix c).toBilin' v w = 0) → v = 0) →
    c = fun _ => 1 := by
  decide +kernel

theorem action_eq_iff (g : MulAut BinaryFour) (B : Form) :
    g • B = B ↔ ∀ v w : V, B.val (linear g v) (linear g w) = B.val v w := by
  constructor
  · intro h v w
    have hh := congrArg (fun C : Form => C.val (linear g v) (linear g w)) h
    change B.val ((linear g).symm (linear g v)) ((linear g).symm (linear g w)) = _ at hh
    simpa using hh.symm
  · intro h
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact (h ((linear g).symm v) ((linear g).symm w)).symm.trans (by simp)

theorem twisted_fixes_base (s : SymmetricFour) : twistedAction s • base = base :=
  (action_eq_iff _ _).mpr (twisted_fixes s)

theorem cycle_fixed_unique (B : Form) (h : twistedAction cycle • B = B) : B = base := by
  have hm : (formMatrix (coordinates B.val)).toBilin' = B.val := by
    rw [← matrix_coordinates, Matrix.toBilin'_toMatrix']
  have hc := fixed_coordinates (coordinates B.val)
    (by rw [hm]; exact (action_eq_iff _ _).mp h)
    (by rw [hm]; exact B.property.2.1)
  apply Subtype.ext
  change B.val = standard
  rw [← hm, hc]
  rfl

theorem twisted_injective : Function.Injective twistedAction := by
  have h : ∀ s : SymmetricFour,
      (∀ i : Fin 4, twistedAction s (Multiplicative.ofAdd (Pi.single i 1)) =
        Multiplicative.ofAdd (Pi.single i 1)) → s = 1 := by
    decide +kernel
  apply (MonoidHom.ker_eq_bot_iff twistedAction).mp
  apply bot_unique
  intro s hs
  apply h
  intro i
  exact congrArg (fun f : MulAut BinaryFour => f (Multiplicative.ofAdd (Pi.single i 1))) hs

theorem cycle_cube : cycle ^ 3 = 1 := by decide +kernel

theorem cycle_ne_one : cycle ≠ 1 := by decide +kernel

end Theory.GroupTheory.HeldM22A10.BinaryRecognition
