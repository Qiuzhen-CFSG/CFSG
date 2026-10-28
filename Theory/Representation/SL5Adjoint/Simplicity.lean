module
public import Theory.Representation.SL5Adjoint.Model
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.HeckeAction.FixedSpace
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Simplicity of the binary SL₅ adjoint representation

Coordinate permutations carry E₀₄ to every off-diagonal matrix unit. A lower
transvection applied to Eᵢ₄ supplies Eᵢᵢ − E₄₄ after subtracting the two
remaining off-diagonal terms. These twenty-four matrices span the trace
kernel, as a direct coordinate expansion proves.

Every nonzero invariant subspace contains a nonzero vector fixed by the
upper unitriangular two-group. `Model.upperFixed_eq_smul` places that vector
on the E₀₄ line. It therefore contains the generating highest-root vector
and equals the entire module. This is a proof for the actual finite matrix
group over F₂, without highest-weight uniqueness or absolute irreducibility.

Source application: Guralnick–Malle, *Classification of 2F-modules, II*,
author manuscript, Lemma 4.5 step 2, pp.23–24. The Chapter K endpoint
realization uses this simplicity theorem in its marked-map assembly.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace Representation.SL5Adjoint
open Matrix
open SL5TenDimensional.Classification

private def permElement (p : Equiv.Perm (Fin 5)) : Group :=
  ⟨p.permMatrix (ZMod 2), by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp <;> rw [hp] <;> decide⟩

private theorem permElement_inv (p : Equiv.Perm (Fin 5)) :
    (permElement p)⁻¹ = permElement p⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change p.permMatrix (ZMod 2) * p⁻¹.permMatrix (ZMod 2) = 1
  rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

private theorem action_perm (p : Equiv.Perm (Fin 5)) (X : Space) (i j : Fin 5) :
    (action (permElement p) X).val i j = X.val (p i) (p j) := by
  rw [action_val, permElement_inv]
  change (((p.toPEquiv.toMatrix : Mat) * X.val) * (p.symm.toPEquiv.toMatrix : Mat)) i j = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

private theorem exists_perm (i j : Fin 5) (hij : i ≠ j) :
    ∃ p : Equiv.Perm (Fin 5), p i = 0 ∧ p j = 4 := by
  let q := Equiv.swap (0 : Fin 5) i
  have hqi : q i = 0 := Equiv.swap_apply_right _ _
  have hqj : q j ≠ 0 := by
    intro hh
    exact hij (q.injective (hqi.trans hh.symm))
  refine ⟨Equiv.swap 4 (q j) * q, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, hqi]
    exact Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hqj)
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]

/-- Every off-diagonal matrix unit is a coordinate-permutation translate of E₀₄. -/
theorem root_mem_of_highestRoot_mem (S : Subrepresentation action)
    (hs : highestRoot ∈ S) (i j : Fin 5) (hij : i ≠ j) : root i j hij ∈ S := by
  obtain ⟨p, hpi, hpj⟩ := exists_perm i j hij
  have he : action (permElement p) highestRoot = root i j hij := by
    apply Subtype.ext
    ext a b
    rw [action_perm]
    simp only [highestRoot, root, Matrix.single, Matrix.of_apply]
    rw [← hpi, ← hpj]
    simp only [Equiv.apply_eq_iff_eq]
  exact he ▸ S.apply_mem_toSubmodule (permElement p) hs

/-- A diagonal trace-zero generator, using the last diagonal coordinate. -/
def diagonal (i : Fin 4) : Space :=
  ⟨Matrix.single i.castSucc i.castSucc 1 - Matrix.single 4 4 1, by
    simp [LinearMap.mem_ker]⟩

private theorem diagonal_action (i : Fin 4) :
    diagonal i =
      action (Matrix.SpecialLinearGroup.transvection
        (show (4 : Fin 5) ≠ i.castSucc by intro h; have hh := congrArg Fin.val h; simp at hh; omega) (1 : ZMod 2))
        (root i.castSucc 4 (by intro h; have hh := congrArg Fin.val h; simp at hh; omega)) -
      root i.castSucc 4 (by intro h; have hh := congrArg Fin.val h; simp at hh; omega) + root 4 i.castSucc (by intro h; have hh := congrArg Fin.val h; simp at hh; omega) := by
  apply Subtype.ext
  change (diagonal i).val =
    (action _ (root i.castSucc 4 _)).val - (root i.castSucc 4 _).val +
      (root 4 i.castSucc _).val
  rw [action_val, Matrix.SpecialLinearGroup.transvection_inv]
  revert i
  decide +kernel

private theorem matrix_expansion (X : Mat) (hX : Matrix.trace X = 0) :
    X = (∑ i : Fin 5, ∑ j : Fin 5,
      if i ≠ j then X i j • Matrix.single i j 1 else 0) +
      ∑ i : Fin 4, X i.castSucc i.castSucc •
        (Matrix.single i.castSucc i.castSucc 1 - Matrix.single 4 4 1) := by
  have ht : X 0 0 + (X 1 1 + (X 2 2 + (X 3 3 + X 4 4))) = 0 := by
    simpa [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_succ] using hX
  have ho (i j : Fin 5) :
      (∑ a : Fin 5, ∑ b : Fin 5,
        if a ≠ b then X a b • Matrix.single a b 1 else (0 : Mat)) i j =
          if i ≠ j then X i j else 0 := by
    change (∑ a : Fin 5, ∑ b : Fin 5,
      (if a ≠ b then X a b • Matrix.single a b 1 else (0 : Mat)) i j) = _
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · split_ifs <;> simp [Matrix.single]
      · intro b _ hb
        split_ifs <;> simp [Matrix.single, hb]
      · simp
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro b _
      split_ifs <;> simp [Matrix.single, ha]
    · simp
  ext i j
  rw [Matrix.add_apply, ho]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, Matrix.single]
  linear_combination (norm := skip) ht
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, neg_zero, sub_zero]

/-- Off-diagonal units and the four diagonal differences span the literal trace kernel. -/
theorem traceZero_expansion (X : Space) :
    X = (∑ i : Fin 5, ∑ j : Fin 5,
      if hij : i ≠ j then X.val i j • root i j hij else 0) +
      ∑ i : Fin 4, X.val i.castSucc i.castSucc • diagonal i := by
  apply Subtype.ext
  have he := matrix_expansion X.val X.property
  convert he using 1
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  congr 1

/-- The highest-root vector generates the entire conjugation representation. -/
theorem eq_top_of_highestRoot_mem (S : Subrepresentation action)
    (hs : highestRoot ∈ S) : S = ⊤ := by
  have hr := root_mem_of_highestRoot_mem S hs
  have hd (i : Fin 4) : diagonal i ∈ S := by
    rw [diagonal_action]
    exact S.toSubmodule.add_mem
      (S.toSubmodule.sub_mem (S.apply_mem_toSubmodule _ (hr _ _ _)) (hr _ _ _))
      (hr _ _ _)
  apply top_unique
  intro X _
  rw [traceZero_expansion X]
  apply S.toSubmodule.add_mem
  · apply S.toSubmodule.sum_mem
    intro i _
    apply S.toSubmodule.sum_mem
    intro j _
    split_ifs with hij
    · exact S.toSubmodule.smul_mem _ (hr _ _ hij)
    · exact S.toSubmodule.zero_mem
  · apply S.toSubmodule.sum_mem
    intro i _
    exact S.toSubmodule.smul_mem _ (hd i)

private theorem upperFixed_val {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) (S : Subrepresentation ρ)
    {x : S.toSubmodule} (hx : UpperFixed S.toRepresentation x) :
    UpperFixed ρ x.val := by
  intro i j hij
  exact congrArg (fun y : S.toSubmodule => y.val) (hx i j hij)

/-- The binary SL₅ trace-zero conjugation module is irreducible. -/
instance action_isIrreducible : IsIrreducible action := by
  let : Nontrivial Space := ⟨⟨highestRoot, 0, highestRoot_ne_zero⟩⟩
  rw [IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  have hS' : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
  let : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS'
  obtain ⟨X, hX, hf⟩ := HeckeAction.exists_nonzero_upperFixed S.toRepresentation
  have hfix : UpperFixed action X.val := upperFixed_val action S hf
  have he := upperFixed_eq_smul hfix
  have hc : X.val.val 0 4 ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact hX (Subtype.ext he)
  apply eq_top_of_highestRoot_mem S
  have hm0 : X.val.val 0 4 • highestRoot ∈ S := he ▸ X.property
  have hm := S.toSubmodule.smul_mem (X.val.val 0 4)⁻¹ hm0
  simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at hm
  exact hm

end Representation.SL5Adjoint
