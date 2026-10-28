module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Diagonal

/-!
# Diagonal quotients of actual basis flags

Changing to the given basis coordinates transports its actual flag stabilizer
to the block-triangular group. The diagonal actions are onto, their kernel is
exactly the intrinsic two-core, and the displayed matrix formula records the
original basis coefficients. This works for every subset of the four cuts.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.25, printed pp.959–960 (PDF pp.976–977).
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.SmallParabolicLevi.TwoNodes
open OuterCyclic FiveFlagGeometry FiveFlagGeometry.SylowOvergroups

/-- Transport an actual basis flag to the standard coordinate flag. -/
noncomputable def flagCoordinates (b : FiveBasis) (cuts : Set (Fin 4)) :
    flagStabilizer b cuts ≃* triangularGroup (cutLabel cuts) :=
  ((MulAut.conj b.equivFun).subgroupMap (flagStabilizer b cuts)).trans
    (MulEquiv.subgroupCongr (by
      change (flagStabilizer b cuts).map (MulAut.conj b.equivFun).toMonoidHom = _
      rw [flagStabilizer_map_conj, triangularGroup_cutLabel]
      congr 1
      ext i j
      simp [standardBasis, Module.Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]))

/-- The diagonal action of the actual basis flag. -/
noncomputable def flagDiagonalAction (b : FiveBasis) (cuts : Set (Fin 4)) :
    flagStabilizer b cuts →* (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (cutLabel cuts) k)) :=
  (diagonalAction (cutLabel cuts)).comp (flagCoordinates b cuts).toMonoidHom

theorem flagDiagonalAction_surjective (b : FiveBasis) (cuts : Set (Fin 4)) :
    Function.Surjective (flagDiagonalAction b cuts) :=
  (diagonalAction_surjective _).comp (flagCoordinates b cuts).surjective

theorem ker_flagDiagonalAction (b : FiveBasis) (cuts : Set (Fin 4)) :
    (flagDiagonalAction b cuts).ker = pCore 2 (flagStabilizer b cuts) := by
  have hc := pCore_map_iso 2 (flagCoordinates b cuts)
  ext g
  change diagonalAction (cutLabel cuts) (flagCoordinates b cuts g) = 1 ↔ _
  rw [← MonoidHom.mem_ker, ker_diagonalAction_eq_twoCore _ (cutLabel_monotone cuts), ← hc]
  simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

noncomputable def flagDiagonalQuotientEquiv (b : FiveBasis) (cuts : Set (Fin 4)) :
    (flagStabilizer b cuts ⧸ pCore 2 (flagStabilizer b cuts)) ≃*
      (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (cutLabel cuts) k)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_flagDiagonalAction b cuts).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (flagDiagonalAction_surjective b cuts))

@[simp] theorem flagDiagonalQuotientEquiv_mk (b : FiveBasis) (cuts : Set (Fin 4))
    (g : flagStabilizer b cuts) :
    flagDiagonalQuotientEquiv b cuts (QuotientGroup.mk' _ g) = flagDiagonalAction b cuts g := rfl


end BinaryLinear.SmallParabolicLevi.TwoNodes
namespace BinaryLinear.SmallParabolicLevi.TwoNodes
open OuterCyclic FiveFlagGeometry FiveFlagGeometry.SylowOvergroups

@[simp] theorem flagCoordinates_apply (b : FiveBasis) (cuts : Set (Fin 4))
    (g : flagStabilizer b cuts) (v : Space 5) :
    (flagCoordinates b cuts g).val v = b.equivFun (g.val (b.equivFun.symm v)) := rfl

/-- Matrix entries after transport are the actual coefficients in the given basis. -/
theorem matrix_flagCoordinates (b : FiveBasis) (cuts : Set (Fin 4))
    (g : flagStabilizer b cuts) (r s : Fin 5) :
    matrix (flagCoordinates b cuts g).val r s = b.equivFun (g.val (b s)) r := by
  rw [matrix_apply, flagCoordinates_apply]
  have he : b.equivFun.symm (standardBasis s) = b s := by
    apply b.equivFun.injective
    ext t
    simp [standardBasis, Module.Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rw [he]

/-- On each marked block the transported action is exactly its diagonal matrix. -/
theorem flagDiagonalAction_apply (b : FiveBasis) (cuts : Set (Fin 4))
    (g : flagStabilizer b cuts) (k : Fin 5) (v : BlockSpace (cutLabel cuts) k)
    (r : Block (cutLabel cuts) k) :
    flagDiagonalAction b cuts g k v r =
      ∑ s : Block (cutLabel cuts) k, b.equivFun (g.val (b s.val)) r.val * v s := by
  change diagonalAction (cutLabel cuts) (flagCoordinates b cuts g) k v r = _
  rw [diagonalAction_apply]
  simp only [matrix_flagCoordinates]

end BinaryLinear.SmallParabolicLevi.TwoNodes

end
