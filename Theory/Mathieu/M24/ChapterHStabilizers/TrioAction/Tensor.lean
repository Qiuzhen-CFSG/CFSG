module

public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction.Kernel
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.TensorSection

/-!
# Tensor coordinates for the native trio translation group

Evaluation sends a pure tensor `a ⊗ n` to the triple `(n i • a)`. Its image
has sum zero because the natural S3 module is the even core on three letters.
The inverse is `∑ i, t i ⊗ beta i`; the zero-sum condition and the decomposition
of the three-letter core prove both inverse identities. This identifies the
translation group itself, independently of the cocode quotient construction.

Source: Aschbacher–Smith H.14.1(3), printed pp.396–397.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped BigOperators TensorProduct
namespace Sporadic.Mathieu.M24ChapterHStabilizers.TrioAction
noncomputable section

def tensorCoordinates : NaturalTensor →ₗ[ZMod 2] (Fin 3 → Vector) :=
  TensorProduct.lift {
    toFun a := {
      toFun n := fun i => n.val i • a
      map_add' n m := by
        funext i
        change (n.val i + m.val i) • a = n.val i • a + m.val i • a
        exact add_smul _ _ _
      map_smul' c n := by
        funext i
        change (c * n.val i) • a = c • (n.val i • a)
        exact mul_smul _ _ _ }
    map_add' a b := by
      apply LinearMap.ext
      intro n
      funext i
      exact smul_add (n.val i) a b
    map_smul' c a := by
      apply LinearMap.ext
      intro n
      funext i
      exact smul_comm (n.val i) c a }

lemma tensorCoordinates_tmul (a : Vector) (n : BinaryPermutation.core (Fin 3)) :
    tensorCoordinates (a ⊗ₜ[ZMod 2] n) = fun i => n.val i • a := rfl

lemma tensorCoordinates_sum_zero (z : NaturalTensor) : ∑ i, tensorCoordinates z i = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a n =>
      rw [tensorCoordinates_tmul, ← Finset.sum_smul]
      have hn := n.property
      rw [BinaryPermutation.mem_core] at hn
      rw [hn, zero_smul]
  | add z w hz hw => simp only [map_add, Pi.add_apply, Finset.sum_add_distrib, hz, hw, add_zero]

def tensorToTranslation : NaturalTensor →ₗ[ZMod 2] translationSpace :=
  tensorCoordinates.codRestrict translationSpace tensorCoordinates_sum_zero

lemma tensorAssembly_coordinates (z : NaturalTensor) :
    tensorAssembly (tensorCoordinates z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a n =>
      rw [tensorCoordinates_tmul]
      change (∑ i, (n.val i • a) ⊗ₜ[ZMod 2] beta i) = _
      simp_rw [TensorProduct.smul_tmul]
      rw [← TensorProduct.tmul_sum, beta_decomposition]
  | add z w hz hw => rw [map_add, map_add, hz, hw]

lemma coordinates_tensorAssembly (t : translationSpace) :
    tensorCoordinates (tensorAssembly t.val) = t.val := by
  funext j
  change tensorCoordinates (∑ i, t.val i ⊗ₜ[ZMod 2] beta i) j = t.val j
  rw [map_sum, Finset.sum_apply, Fin.sum_univ_three]
  simp only [tensorCoordinates_tmul]
  funext k
  fin_cases j <;>
    simp [beta_apply, translationSpace_last, Pi.add_apply, add_left_comm,
      CharTwo.add_self_eq_zero, CharTwo.add_cancel_left]

def tensorTranslationEquiv : NaturalTensor ≃ₗ[ZMod 2] translationSpace :=
  LinearEquiv.ofBijective tensorToTranslation ⟨by
    intro z w h
    rw [← tensorAssembly_coordinates z, ← tensorAssembly_coordinates w]
    exact congrArg tensorAssembly (congrArg Subtype.val h), by
    intro t
    exact ⟨tensorAssembly t.val, Subtype.ext (coordinates_tensorAssembly t)⟩⟩

end
end Sporadic.Mathieu.M24ChapterHStabilizers.TrioAction
