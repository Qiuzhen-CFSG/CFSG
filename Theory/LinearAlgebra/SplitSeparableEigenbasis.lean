module
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# An eigenbasis from a split separable annihilator

The kernels of the distinct linear factors form a direct sum. Collecting bases
of these kernels gives an eigenbasis over the original coefficient field.
This is the common diagonalization step for the scalar-cube arguments in
Aschbacher–Smith A.3.18, printed pp.52–53, extracted from the checked linear
cover proof without changing that proof's mathematical interface.
-/

public noncomputable section
open Polynomial Matrix
namespace Module.End

private theorem ker_split_product {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (f : Module.End F V) (s : Finset F) :
    LinearMap.ker (aeval f (∏ a ∈ s, (X - C a))) = ⨆ a ∈ s, f.eigenspace a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime]
    · simp only [aeval_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
        ← Module.End.eigenspace_def, ih]
      simp only [Finset.mem_insert, iSup_or, iSup_sup_eq, iSup_iSup_eq_left]
    · apply IsCoprime.prod_right
      intro b hb
      exact isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr (ne_of_mem_of_not_mem hb ha).symm).isUnit

/-- A split separable annihilating polynomial gives a basis of actual eigenvectors. -/
theorem exists_eigenbasis_of_split_separable_annihilator {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (f : Module.End F V) (p : F[X]) (hm : p.Monic) (hs : p.Splits)
    (hp : p.Separable) (hz : aeval f p = 0) :
    ∃ (b : Module.Basis (Fin (Module.finrank F V)) F V)
      (μ : Fin (Module.finrank F V) → F), ∀ i, f (b i) = μ i • b i := by
  classical
  let s : Finset F := ⟨p.roots, Polynomial.nodup_roots hp⟩
  have he : (∏ a ∈ s, (X - C a)) = p := (hs.eq_prod_roots_of_monic hm).symm
  have ht : (⨆ a, f.eigenspace a) = ⊤ := by
    apply top_unique
    calc
      (⊤ : Submodule F V) = LinearMap.ker (aeval f (∏ a ∈ s, (X - C a))) := by
        rw [he,hz,LinearMap.ker_zero]
      _ = ⨆ a ∈ s, f.eigenspace a := ker_split_product f s
      _ ≤ ⨆ a, f.eigenspace a := iSup_le fun a => iSup_le fun _ => le_iSup _ a
  let hd := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top f.eigenspaces_iSupIndep ht
  let I := (a : F) × Fin (Module.finrank F (f.eigenspace a))
  let b : Module.Basis I F V := hd.collectedBasis fun a => Module.finBasis F (f.eigenspace a)
  let : Fintype I := FiniteDimensional.fintypeBasisIndex b
  let e : I ≃ Fin (Module.finrank F V) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  refine ⟨b.reindex e,fun i => (e.symm i).1,?_⟩
  intro i
  have hb := hd.collectedBasis_mem (fun a => Module.finBasis F (f.eigenspace a)) (e.symm i)
  simpa only [Module.Basis.reindex_apply] using Module.End.mem_eigenspace_iff.mp hb

end Module.End
