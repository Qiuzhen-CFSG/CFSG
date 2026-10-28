module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.TrivialTwoCore.NormalizerAction.Coordinates
public import Theory.AtlasPort.ExceptionalIsomorphisms.PSL2NineAction

/-!
# The quadratic normalizer on the ten extension-field lines

Line preservation in the quadratic coordinates descends the actual matrix
action to the projective line. The ATLAS marking numbers its ten points. We
also compute quadratic conjugation in this marking and identify it with the
complementary-triple action of the transposition `(4 5)` on six labels.

The marking and comparison action come from the ATLAS ports `PSL2NineAction`
and `TriplePartitions`: Gerald Höhn and the ATLAS contributors, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, ATLAS Research and Attribution License
1.0 (`LICENSES/ATLAS.txt`). The new finite checks enumerate only the ten points.
Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4/482 of `refs/quasithin.pdf`.
-/

@[expose] public section

noncomputable section
open Matrix
open scoped LinearAlgebra.Projectivization MatrixGroups Pointwise
namespace Matrix.PSp4Three.TrivialTwoCore.NormalizerAction
open Atlas.Comparisons.Exceptional

private theorem transport_ne_zero (g : Sp 2 (ZMod 3)) {w : W} (hw : w ≠ 0) :
    transport g w ≠ 0 := by
  exact (map_ne_zero_iff (transport g) (transport g).injective).mpr hw

def lineMap (g : quadraticNormalizer) : Nine.L → Nine.L :=
  Projectivization.lift
    (fun w => Projectivization.mk Nine.F (transport g.val w.val) (by exact transport_ne_zero _ w.property))
    (by
      intro u v a huv
      apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
      obtain ⟨b, hb⟩ := transport_scalar g a v.val
      exact ⟨b, by rw [huv, hb]⟩)

@[simp] theorem lineMap_mk (g : quadraticNormalizer) (w : W) (hw : w ≠ 0) :
    lineMap g (Projectivization.mk Nine.F w hw) =
      Projectivization.mk Nine.F (transport g.val w) (by exact transport_ne_zero _ hw) := rfl

instance normalizerLineAction : MulAction quadraticNormalizer Nine.L where
  smul := lineMap
  one_smul p := by
    change lineMap 1 p = p
    induction p using Projectivization.ind with
    | h w hw => simp only [lineMap_mk, Subgroup.coe_one, transport_one]
  mul_smul g h p := by
    change lineMap (g * h) p = lineMap g (lineMap h p)
    induction p using Projectivization.ind with
    | h w hw => simp only [lineMap_mk, Subgroup.coe_mul, transport_mul]

def tenPointAction : quadraticNormalizer →* Equiv.Perm (Fin 10) :=
  Nine.marking.symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom quadraticNormalizer Nine.L)

theorem tenPointAction_marking (g : quadraticNormalizer) (i : Fin 10) :
    Nine.marking (tenPointAction g i) = lineMap g (Nine.marking i) :=
  Nine.marking.apply_symm_apply _

theorem tenPointAction_point (g : quadraticNormalizer) (i : Fin 10) :
    Nine.point (tenPointAction g i) =
      Projectivization.mk Nine.F (transport g.val (Nine.pointVector i))
        (by exact transport_ne_zero _ (Nine.pointVector_ne i)) :=
  tenPointAction_marking g i

/-- Conjugation exchanges the two nonreal rows of the affine marking. -/
def conjugationPermutation : Equiv.Perm (Fin 10) where
  toFun := ![0, 1, 2, 6, 7, 8, 3, 4, 5, 9]
  invFun := ![0, 1, 2, 6, 7, 8, 3, 4, 5, 9]
  left_inv := by decide
  right_inv := by decide

theorem conjugation_pointVector (i : Fin 10) :
    (fun j => star (Nine.pointVector i j)) = Nine.pointVector (conjugationPermutation i) := by
  have h : ∀ i : Fin 10,
      (fun j => star (Nine.pointVector i j)) = Nine.pointVector (conjugationPermutation i) := by
    decide
  exact h i

theorem tenPointAction_conjugation : tenPointAction conjugationElement = conjugationPermutation := by
  apply Equiv.ext
  intro i
  apply Nine.marking.injective
  rw [tenPointAction_marking]
  change lineMap conjugationElement (Nine.point i) = Nine.point (conjugationPermutation i)
  simp only [Nine.point, lineMap_mk, conjugationElement, transport_conjugation,
    conjugation_pointVector]

/-- The odd coset uses the ordinary transposition of the last two six-point labels. -/
theorem symmetricAction_swap :
    TriplePartitions.symmetricAction (Equiv.swap (4 : Fin 6) 5) = conjugationPermutation := by
  apply Equiv.ext
  intro i
  apply TriplePartitions.symmetricAction_eq
  have h : ∀ i : Fin 10,
      (Equiv.swap (4 : Fin 6) 5) • TriplePartitions.pair (TriplePartitions.triple i) =
        TriplePartitions.pair (TriplePartitions.triple (conjugationPermutation i)) := by decide
  exact h i

theorem tenPointAction_eq_of_matrix (g : quadraticNormalizer) (A : SL(2, Nine.F))
    (hA : ∀ w : W, transport g.val w = A.val *ᵥ w) :
    tenPointAction g = Nine.permutation (A : PSL(2, Nine.F)) := by
  apply Equiv.ext
  intro i
  apply Nine.marking.injective
  rw [tenPointAction_marking]
  change lineMap g (Nine.point i) =
    Nine.marking (Nine.marking.symm ((A : PSL(2, Nine.F)) • Nine.point i))
  rw [Nine.marking.apply_symm_apply]
  simp only [Nine.point, lineMap_mk, Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,
    Projectivization.smul_mk]
  congr 1
  exact hA _

end Matrix.PSp4Three.TrivialTwoCore.NormalizerAction
