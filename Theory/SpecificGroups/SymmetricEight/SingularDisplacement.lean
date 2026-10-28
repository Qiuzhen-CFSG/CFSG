module
public import Theory.SpecificGroups.ClassicalOrthogonal.BinaryD3Comparison
import all Theory.SpecificGroups.ClassicalOrthogonal.BinaryD3Comparison

/-!
# Singular displacement in the deleted eight-point module

If a permutation fixes i and moves j, the displacement of the duad {i,j}
is the duad {j,g(j)}, whose quadratic value is one. Thus a nonidentity
permutation whose entire displacement is singular has no fixed point.
The result is transported through the actual deleted-module isometry to
the standard split six-space used by the orthogonal comparison.
-/

public noncomputable section
namespace ClassicalOrthogonal.BinaryD3Comparison
open Atlas.Order20160A8 Atlas.Order20160A8.DeletedEight
open Atlas.Order20160A8.HalfWeight Atlas.Codes

private theorem duad_halfWeight (i j : Fin 8) (hij : i ≠ j) :
    binaryHalfWeight (duadVector i j) = 1 := by
  have hh : ∀ i j : Fin 8, i ≠ j → binaryHalfWeight (duadVector i j) = 1 := by
    decide +kernel
  exact hh i j hij

private theorem duad_sub_common (i j k : Fin 8) :
    duad i k - duad i j = duad k j := by
  apply Subtype.ext
  change duadVector i k - duadVector i j = duadVector k j
  ext t
  simp only [duadVector,Pi.sub_apply,Pi.add_apply]
  have hh (a b c : Bit) : (a+b)-(a+c)=b-c := by abel
  rw [hh,CharTwo.sub_eq_add]

private theorem deleted_fixedPointFree_of_singular_displacement
    (p : Equiv.Perm (Fin 8)) (hp : p ≠ 1)
    (hs : ∀ v : W, quotientQuadratic ((permutationHom p).val v - v) = 0) :
    ∀ i, p i ≠ i := by
  intro i hi
  obtain ⟨j,hj⟩ : ∃ j, p j ≠ j := by
    by_contra! h
    apply hp
    apply Equiv.ext
    intro j
    exact h j
  have hh := hs (Submodule.Quotient.mk (duad i j))
  change quotientQuadratic
    (Submodule.Quotient.mk (evenPerm p (duad i j)) -
      Submodule.Quotient.mk (duad i j)) = 0 at hh
  rw [duad_permute,hi,←Submodule.Quotient.mk_sub,duad_sub_common,
    quotientQuadratic_mk] at hh
  exact one_ne_zero ((duad_halfWeight (p j) j hj).symm.trans hh)

/-- In the actual split-six realization of S8, a nonidentity permutation
with totally singular displacement fixes none of the original eight points. -/
theorem fixedPointFree_of_singular_displacement
    (p : Equiv.Perm (Fin 8)) (hp : p ≠ 1)
    (hs : ∀ v : ClassicalOrthogonal.VectorD 3 (ZMod 2),
      ClassicalOrthogonal.formD 3 (ZMod 2) ((symmetricEquiv p).val v - v) = 0) :
    ∀ i, p i ≠ i := by
  apply deleted_fixedPointFree_of_singular_displacement p hp
  intro w
  have hh := hs (splitIsometry.symm w)
  change ClassicalOrthogonal.formD 3 (ZMod 2)
    (splitIsometry.symm ((permutationHom p).val (splitIsometry (splitIsometry.symm w))) -
      splitIsometry.symm w) = 0 at hh
  rw [splitIsometry.apply_symm_apply,←map_sub,splitIsometry.symm.map_app] at hh
  exact hh

end ClassicalOrthogonal.BinaryD3Comparison
