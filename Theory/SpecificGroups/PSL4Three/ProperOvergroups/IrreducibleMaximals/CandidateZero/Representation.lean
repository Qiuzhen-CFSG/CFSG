module

public import Theory.SpecificGroups.PSL4Three.ProperOvergroups.IrreducibleMaximals.CandidateZero.Forms
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The symplectic representation of the four-form kernel

Reindexing `Fin 4` by `Fin 2 ⊕ Fin 2` identifies the first form with the
standard symplectic matrix, up to sign. The form-action kernel therefore embeds
in the actual symplectic matrix group. Its map to PSp₄(3) has solvable kernel,
since that kernel embeds in the symplectic center. Every scalar matrix killed
by SL₄(3) → PSL₄(3) is also killed by this projective symplectic map.

Source application: Aschbacher–Smith, Theorem 0.1.2(4) and condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals.CandidateZero

private def reindex : Mat ≃+* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  Matrix.reindexRingEquiv (ZMod 3) (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm

private theorem reindex_transpose (M : Mat) : reindex Mᵀ = (reindex M)ᵀ := rfl

private theorem reindex_form : reindex (formMatrix 0) = -Matrix.J (Fin 2) (ZMod 3) := by
  decide

private theorem kernel_symplectic (g : action.ker) :
    reindex (g.val.val : Mat) ∈ symplecticGroup (Fin 2) (ZMod 3) := by
  apply SymplecticGroup.mem_iff'.mpr
  have h := congrArg reindex (action_ker_preserves g)
  rw [map_mul, map_mul, reindex_transpose, reindex_form] at h
  simpa only [Matrix.mul_neg, Matrix.neg_mul, neg_inj] using h

/-- Reindexing the natural matrices embeds the kernel in the symplectic group. -/
public noncomputable def symplectic : action.ker →* symplecticGroup (Fin 2) (ZMod 3) where
  toFun g := ⟨reindex (g.val.val : Mat), kernel_symplectic g⟩
  map_one' := by apply Subtype.ext; exact map_one reindex
  map_mul' g h := by apply Subtype.ext; exact map_mul reindex _ _

public theorem symplectic_injective : Function.Injective symplectic := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply reindex.injective
  exact congrArg Subtype.val he

/-- The homomorphism into the actual central symplectic quotient. -/
public noncomputable def projectiveSymplectic : action.ker →* Matrix.PSL4Three.PSp :=
  (QuotientGroup.mk' _).comp symplectic

public theorem projectiveSymplectic_ker_solvable : Group.IsSolvable projectiveSymplectic.ker := by
  let k : projectiveSymplectic.ker →* Subgroup.center (symplecticGroup (Fin 2) (ZMod 3)) :=
    (symplectic.comp projectiveSymplectic.ker.subtype).codRestrict _ (fun x =>
      (QuotientGroup.eq_one_iff (symplectic x.val)).mp x.property)
  let : Group.IsSolvable (Subgroup.center (symplecticGroup (Fin 2) (ZMod 3))) :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext
      (Subgroup.mem_center_iff.mp a.property b.val).symm)
  apply Group.isSolvable_of_isSolvable_injective (f := k)
  intro x y h
  apply Subtype.ext
  apply symplectic_injective
  exact congrArg Subtype.val h

private theorem reindex_scalar (a : ZMod 3) :
    reindex (Matrix.scalar (Fin 4) a) = Matrix.scalar (Fin 2 ⊕ Fin 2) a := by
  simp [reindex, Matrix.reindex_apply, Matrix.scalar_apply]

/-- Every scalar killed in PSL is also killed in the projective symplectic group. -/
public theorem projectiveSymplectic_eq_one (g : action.ker)
    (hg : project g.val.val = 1) : projectiveSymplectic g = 1 := by
  have hz : g.val.val ∈ Subgroup.center SL := (QuotientGroup.eq_one_iff _).mp hg
  obtain ⟨a, _, ha⟩ := SpecialLinearGroup.mem_center_iff.mp hz
  apply (QuotientGroup.eq_one_iff (symplectic g)).mpr
  apply Subgroup.mem_center_iff.mpr
  intro h
  apply Subtype.ext
  change (h.val : Matrix _ _ _) * reindex (g.val.val : Mat) =
    reindex (g.val.val : Mat) * h.val
  rw [← ha, reindex_scalar]
  exact (Matrix.scalar_commute a (Commute.all a) h.val).symm.eq

end Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals.CandidateZero
