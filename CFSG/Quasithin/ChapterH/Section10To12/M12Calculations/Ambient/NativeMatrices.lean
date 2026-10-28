module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.Centralizer
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Automorphisms
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Checked generator matrices for the M₁₂ heart extension

The two literal degree-24 automorphism generators act on the ten heart
coordinates by the matrices given below. Their inverse identities and their
intertwining identities on a basis are checked in the kernel. Conjugation on
the marked inner generators is checked in the actual degree-24 carrier using
short words, then transported through its proved full automorphism equivalence.
No permutation action of outer automorphisms on twelve letters is used.

The matrices were obtained by solving the two intertwining equations over F₂;
only the displayed checked equations enter the proofs. The permutation seeds
are the existing ATLAS M12d2G1-p24B0 model. Source context: Aschbacher–Smith
H.11.1, printed pp.392–393 (1 March 2004 manuscript).
-/

public section

namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.NativeMatrices
open Sporadic.Mathieu M12ExceptionalExtension

@[expose] def generator (i : Fin 2) : Carrier :=
  if i = 0 then ⟨generatorA, Subgroup.subset_closure (by simp)⟩
  else ⟨generatorB, Subgroup.subset_closure (by simp)⟩

@[expose] noncomputable def original (j : Fin 2) : M12 := if j = 0 then originalA else originalB

private def conjugateWord : Fin 2 → Fin 2 → List Bool := ![
  ![[true, false, true, true, false, true, false, true, true, false, true, false, true, true], [true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false]],
  ![[true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, true], [true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true]]]

private def perm00 : Equiv.Perm (Fin 12) where
  toFun := ![3, 4, 8, 0, 1, 5, 10, 7, 2, 9, 6, 11]
  invFun := ![3, 4, 8, 0, 1, 5, 10, 7, 2, 9, 6, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def perm01 : Equiv.Perm (Fin 12) where
  toFun := ![10, 6, 9, 0, 11, 1, 5, 2, 4, 7, 3, 8]
  invFun := ![3, 5, 7, 10, 8, 6, 1, 9, 11, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def perm10 : Equiv.Perm (Fin 12) where
  toFun := ![0, 7, 3, 2, 10, 8, 6, 1, 5, 9, 4, 11]
  invFun := ![0, 7, 3, 2, 10, 8, 6, 1, 5, 9, 4, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def perm11 : Equiv.Perm (Fin 12) where
  toFun := ![10, 9, 0, 7, 8, 4, 3, 6, 5, 11, 2, 1]
  invFun := ![2, 11, 10, 6, 5, 8, 7, 3, 4, 1, 0, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def conjugatePerm (i j : Fin 2) : Equiv.Perm (Fin 12) :=
  ![![perm00, perm01], ![perm10, perm11]] i j

private theorem conjugate_word_spec : ∀ i j : Fin 2,
    generator i * (if j = 0 then innerA else innerB) * (generator i)⁻¹ =
      evaluate innerA innerB (conjugateWord i j) := by
  intro i j
  apply Subtype.ext
  revert i j
  decide +kernel

private theorem conjugate_perm_spec : ∀ i j : Fin 2,
    evaluate m12GeneratorA m12GeneratorB (conjugateWord i j) = conjugatePerm i j := by
  decide +kernel

private theorem embedding_action (g : Carrier) (x : M12) :
    innerModel.embedding (automorphismEquiv g x) =
      g * innerModel.embedding x * g⁻¹ := by
  apply automorphismEquiv.injective
  simp only [automorphismEquiv_embedding, map_mul, map_inv]
  ext y
  simp [MulAut.conj_apply]

private theorem automorphism_original (i j : Fin 2) :
    (automorphismEquiv (generator i) (original j)).val = conjugatePerm i j := by
  have he : automorphismEquiv (generator i) (original j) =
      evaluate originalA originalB (conjugateWord i j) := by
    apply innerModel.embedding_injective
    rw [embedding_action, map_evaluate,
      innerModel.embedding_originalA, innerModel.embedding_originalB]
    have hg : innerModel.embedding (original j) = if j = 0 then innerA else innerB := by
      simp only [original]
      split_ifs <;> simp only [innerModel.embedding_originalA, innerModel.embedding_originalB]
    rw [hg]
    exact conjugate_word_spec i j
  have hv := congrArg Subtype.val he
  change (automorphismEquiv (generator i) (original j)).val =
    M12.subtype (evaluate originalA originalB (conjugateWord i j)) at hv
  rw [map_evaluate] at hv
  exact hv.trans (conjugate_perm_spec i j)

private def rows : Fin 2 → Fin 10 → ℕ := ![![730, 872, 409, 342, 819, 227, 965, 692, 527, 125],
  ![192, 66, 64, 72, 65, 96, 68, 80, 959, 320]]
private def inverseRows : Fin 2 → Fin 10 → ℕ := ![![730, 872, 409, 342, 819, 227, 965, 692, 527, 125],
  ![20, 6, 68, 12, 132, 36, 4, 5, 516, 1019]]

private def binaryMatrix (r : Fin 10 → ℕ) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun i j => if (r i).testBit j.val then 1 else 0

private def matrix (i : Fin 2) := binaryMatrix (rows i)
private def inverseMatrix (i : Fin 2) := binaryMatrix (inverseRows i)

private theorem inverse_left : ∀ i : Fin 2, inverseMatrix i * matrix i = 1 := by decide +kernel
private theorem inverse_right : ∀ i : Fin 2, matrix i * inverseMatrix i = 1 := by decide +kernel

private def coordinateEquiv (i : Fin 2) : Coordinates ≃ₗ[ZMod 2] Coordinates :=
  LinearEquiv.ofLinearMap (matrix i).mulVecLin (inverseMatrix i).mulVecLin
    (by rw [← Matrix.mulVecLin_mul, inverse_right, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, inverse_left, Matrix.mulVecLin_one])

private theorem intertwines_basis : ∀ i j : Fin 2, ∀ k : Fin 10,
    (matrix i).mulVecLin (action (if j = 0 then m12GeneratorA else m12GeneratorB) (Pi.single k 1)) =
      action (conjugatePerm i j) ((matrix i).mulVecLin (Pi.single k 1)) := by decide +kernel

private theorem coordinate_intertwines (i j : Fin 2) (v : Coordinates) :
    coordinateEquiv i (coordinateRepresentation (original j) v) =
      action (conjugatePerm i j) (coordinateEquiv i v) := by
  have he : (matrix i).mulVecLin.comp
      (action (if j = 0 then m12GeneratorA else m12GeneratorB)) =
      (action (conjugatePerm i j)).comp (matrix i).mulVecLin := by
    apply LinearMap.pi_ext
    intro k x
    have hx : (Pi.single k x : Coordinates) = x • Pi.single k 1 := by
      ext l
      simp [Pi.single_apply]
    rw [hx]
    simp only [map_smul, LinearMap.comp_apply, intertwines_basis]
  have hv := congrArg (fun f : Module.End (ZMod 2) Coordinates => f v) he
  change (matrix i).mulVecLin
    (action (if j = 0 then m12GeneratorA else m12GeneratorB) v) = _ at hv
  have hp : (original j).val = if j = 0 then m12GeneratorA else m12GeneratorB := by
    simp only [original]
    split_ifs <;> rfl
  change (matrix i).mulVecLin (action (original j).val v) = _
  rw [hp]
  exact hv

noncomputable def heartEquiv (i : Fin 2) : M12Heart ≃ₗ[ZMod 2] M12Heart :=
  M12Calculations.heartEquiv.symm.trans ((coordinateEquiv i).trans M12Calculations.heartEquiv)

theorem heart_intertwines (i j : Fin 2) (v : M12Heart) :
    heartEquiv i (m12HeartRepresentation (original j) v) =
      m12HeartRepresentation (automorphismEquiv (generator i) (original j)) (heartEquiv i v) := by
  obtain ⟨u, rfl⟩ := M12Calculations.heartEquiv.surjective v
  have hh (g : M12) (w : Coordinates) :
      m12HeartRepresentation g (M12Calculations.heartEquiv w) =
        M12Calculations.heartEquiv (coordinateRepresentation g w) :=
    (M12Calculations.heartEquiv_action g.val w).symm
  simp only [hh, heartEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [coordinate_intertwines]
  change M12Calculations.heartEquiv (action (conjugatePerm i j) (coordinateEquiv i u)) =
    M12Calculations.heartEquiv
      (action (automorphismEquiv (generator i) (original j)).val (coordinateEquiv i u))
  rw [automorphism_original]

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.NativeMatrices
