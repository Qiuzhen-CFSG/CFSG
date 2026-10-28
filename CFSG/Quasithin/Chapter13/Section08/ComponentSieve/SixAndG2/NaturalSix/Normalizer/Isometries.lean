module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer.Pairing
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Isometries of the actual six-letter natural module

The duad vectors 01, 34, 02, 35 give a symplectic basis of the augmentation
quotient, with Gram matrix `Matrix.J`. Thus its pairing isometries inject
into the actual matrix group Sp₄(2), whose proved order is 720. The faithful
symmetric natural action supplies 720 isometries, so supplies all of them.
This proves the identification on the original module and preserves its
literal symmetric embedding.

This is the isometry half of the normalizer calculation used in
Aschbacher–Smith 13.8.26–27, printed pp.962–963; the natural-module convention
is §B.3, printed pp.83–85. The symplectic order theorem is the independent
hyperbolic-pair counting argument, not a classification of overgroups.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open scoped Matrix

private abbrev Index := Fin 2 ⊕ Fin 2

private def frame : Index → Natural :=
  Sum.elim ![pairVector 0 1, pairVector 3 4] ![pairVector 0 2, pairVector 3 5]

private theorem frame_dual (i j : Index) :
    pairing (frame ((Equiv.sumComm (Fin 2) (Fin 2)) i)) (frame j) =
      if j = i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [frame, pairing_pairVector] <;> decide

private theorem frame_independent : LinearIndependent (ZMod 2) frame := by
  apply Fintype.linearIndependent_iff.mpr
  intro f hf i
  have he := congrArg (pairing (frame ((Equiv.sumComm (Fin 2) (Fin 2)) i))) hf
  simpa only [map_sum, map_smul, frame_dual, map_zero, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using he

private noncomputable def symplecticBasis : Module.Basis Index (ZMod 2) Natural :=
  basisOfLinearIndependentOfCardEqFinrank frame_independent (by rw [natural_finrank]; decide)

private theorem symplecticBasis_apply (i : Index) : symplecticBasis i = frame i := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i

private theorem pairing_matrix :
    LinearMap.BilinForm.toMatrix symplecticBasis pairing = Matrix.J (Fin 2) (ZMod 2) := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, symplecticBasis_apply, symplecticBasis_apply]
  fin_cases i <;> fin_cases j <;>
    simp [frame, pairing_pairVector, Matrix.J, Matrix.fromBlocks] <;> decide

/-- The isometries of the actual descended pairing, retaining their linear operators. -/
def PairingIsometry := {u : LinearGroup // ∀ v w,
  pairing (u.val v) (u.val w) = pairing v w}

private noncomputable def isometryMatrix (u : PairingIsometry) :
    Matrix.symplecticGroup (Fin 2) (ZMod 2) :=
  ⟨LinearMap.toMatrix symplecticBasis symplecticBasis u.val.val, by
    rw [SymplecticGroup.mem_iff']
    have he : LinearMap.BilinForm.comp pairing u.val.val u.val.val = pairing := by
      ext v w
      exact u.property v w
    have hm := congrArg (LinearMap.BilinForm.toMatrix symplecticBasis) he
    rw [LinearMap.BilinForm.toMatrix_comp symplecticBasis symplecticBasis,
      pairing_matrix] at hm
    exact hm⟩

private theorem isometryMatrix_injective : Function.Injective isometryMatrix := by
  intro u v huv
  apply Subtype.ext
  apply Units.ext
  exact (LinearMap.toMatrix symplecticBasis symplecticBasis).injective (congrArg Subtype.val huv)

/-- There are at most 720 isometries: an explicit symplectic basis embeds them in Sp₄(2). -/
theorem card_pairingIsometry_le : Nat.card PairingIsometry ≤ 720 := by
  have h := Nat.card_le_card_of_injective isometryMatrix isometryMatrix_injective
  have hc : Nat.card (Matrix.symplecticGroup (Fin 2) (ZMod 2)) = 720 := by
    have hsp := Theory.SpecificGroups.SymplecticFour.card_sp (ZMod 2)
    norm_num [Nat.card_eq_fintype_card, ZMod.card] at hsp
    exact hsp
  exact hc ▸ h

/-- Every isometry of the actual natural module is induced by a permutation of six letters. -/
theorem isometry_mem_symmetricImage (u : LinearGroup)
    (hu : ∀ v w, pairing (u.val v) (u.val w) = pairing v w) :
    u ∈ symmetricImage := by
  let f : Symmetric → PairingIsometry := fun g =>
    ⟨symmetricHom g, pairing_invariant g⟩
  have hf : Function.Injective f := by
    intro g h he
    exact symmetricHom_injective (congrArg Subtype.val he)
  have : Finite PairingIsometry := Finite.of_injective isometryMatrix isometryMatrix_injective
  have hcard : Nat.card PairingIsometry ≤ Nat.card Symmetric := by
    have hs : Nat.card Symmetric = 720 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      decide
    rw [hs]
    exact card_pairingIsometry_le
  obtain ⟨g, hg⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨u, hu⟩
  exact ⟨g, congrArg Subtype.val hg⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
