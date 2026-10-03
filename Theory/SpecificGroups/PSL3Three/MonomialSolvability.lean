module

public import Theory.SpecificGroups.PSL3Three.Subgroups
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Solvability of the monomial subgroup in PSL₃(3)

The stabilizer of the six signed coordinate vectors permutes their three
opposite pairs, the coordinate axes. The kernel of this permutation action
consists of diagonal matrices, so its elements commute. The permutation image
is solvable: the symmetric group on three letters embeds in the solvable
symmetric group on four letters. Solvability of extensions and homomorphic
images then gives the result for the specified subgroup of PSL₃(3).

Only the small vector calculations identifying the six signed coordinate
vectors use finite kernel reduction. The action, its diagonal kernel, and
solvability of the full setwise stabilizer are proved structurally.

Source: GLS, volume III, Theorem 6.5.3(b), in
`refs/KGroup/GLS3/chapter6.tex`.
-/

open scoped Pointwise

namespace Matrix.PSL3Three

private abbrev Vec := Fin 3 → ZMod 3
private def basisVector (i : Fin 3) : Vec := Pi.single i 1
private def axis (i : Fin 3) : Set Vec := {basisVector i, -basisVector i}

private theorem norm_one_signed : ∀ v : Vec,
    v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 →
      ∃ i, v = basisVector i ∨ v = -basisVector i := by decide

private theorem basis_norm : ∀ i : Fin 3,
    (basisVector i) 0 ^ 2 + (basisVector i) 1 ^ 2 +
      (basisVector i) 2 ^ 2 = 1 := by decide

private theorem axis_injective : Function.Injective axis := by
  have h : ∀ i j : Fin 3, basisVector i = basisVector j ∨
      basisVector i = -basisVector j → i = j := by decide
  intro i j hij
  apply h i j
  have hi : basisVector i ∈ axis i := by simp [axis]
  rw [hij] at hi
  simpa [axis] using hi

private theorem smul_axis (g : monomialSL) (i : Fin 3) :
    ∃ j, (g : SL) • axis i = axis j := by
  have hg : (g : SL) • {v : Vec | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1} =
      {v : Vec | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1} := g.property
  have hv := Set.smul_mem_smul_set (a := (g : SL))
    (show basisVector i ∈ {v : Vec | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1}
      from basis_norm i)
  rw [hg] at hv
  obtain ⟨j, hj | hj⟩ := norm_one_signed _ hv
  · exact ⟨j, by simp [axis, Set.smul_set_insert, Set.smul_set_singleton, smul_neg, hj]⟩
  · exact ⟨j, by simp [axis, Set.smul_set_insert, Set.smul_set_singleton, smul_neg, hj,
      Set.pair_comm]⟩

private def axes : SubMulAction monomialSL (Set Vec) where
  carrier := Set.range axis
  smul_mem' g _ hs := by
    obtain ⟨i, rfl⟩ := hs
    obtain ⟨j, hj⟩ := smul_axis g i
    exact ⟨j, hj.symm⟩

private def axisAction : monomialSL →* Equiv.Perm axes :=
  MulAction.toPermHom monomialSL axes

private noncomputable def axesEquiv : Fin 3 ≃ axes :=
  Equiv.ofInjective axis axis_injective

private theorem axes_perm_solvable : Group.IsSolvable (Equiv.Perm axes) := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let e : axes ↪ Fin 4 :=
    ⟨fun a => Fin.castSucc (axesEquiv.symm a),
      fun _ _ h => axesEquiv.symm.injective (Fin.castSucc_inj.mp h)⟩
  exact Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)

private theorem kernel_diagonal (g : axisAction.ker) (i j : Fin 3) (hij : i ≠ j) :
    g.val.val i j = 0 := by
  have hg : axisAction g.val = 1 := g.property
  have ha := congrArg (fun p : Equiv.Perm axes => p ⟨axis j, ⟨j, rfl⟩⟩) hg
  have hs : (g.val : SL) • axis j = axis j := congrArg Subtype.val ha
  have hv : (g.val : SL) • basisVector j ∈ axis j := by
    rw [← hs]
    exact Set.smul_mem_smul_set (by simp [axis])
  have hz : ∀ v : Vec, v ∈ axis j → v i = 0 := by
    intro v hv
    rcases hv with rfl | hv
    · simp [basisVector, hij]
    · have hv' : v = -basisVector j := hv
      simp [hv', basisVector, hij]
  have hzero := hz _ hv
  simpa [SpecialLinearGroup.smul_def, basisVector, Matrix.mulVec_single] using hzero

private theorem kernel_comm (g h : axisAction.ker) : g * h = h * g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  have hg : g.val.val.val = Matrix.diagonal (fun i => g.val.val i i) := by
    ext i j
    by_cases hij : i = j
    · simp [hij]
    · simp [Matrix.diagonal_apply_ne _ hij, kernel_diagonal g i j hij]
  have hh : h.val.val.val = Matrix.diagonal (fun i => h.val.val i i) := by
    ext i j
    by_cases hij : i = j
    · simp [hij]
    · simp [Matrix.diagonal_apply_ne _ hij, kernel_diagonal h i j hij]
  change g.val.val.val * h.val.val.val = h.val.val.val * g.val.val.val
  rw [hg, hh, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/-- The signed monomial subgroup of SL₃(3) is solvable. -/
public theorem monomialSL_isSolvable : Group.IsSolvable monomialSL := by
  let : Group.IsSolvable (Equiv.Perm axes) := axes_perm_solvable
  let : Group.IsSolvable axisAction.ker := Group.isSolvable_of_comm kernel_comm
  exact Group.isSolvable_of_ker_le_range axisAction.ker.subtype axisAction (by
    rw [Subgroup.range_subtype])

/-- The specified monomial subgroup of PSL₃(3) is solvable. -/
public theorem monomial_isSolvable : Group.IsSolvable monomial := by
  let := monomialSL_isSolvable
  exact Group.isSolvable_of_surjective (project.subgroupMap_surjective monomialSL)

end Matrix.PSL3Three
