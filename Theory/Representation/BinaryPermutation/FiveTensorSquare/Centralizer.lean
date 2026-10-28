module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Model
public import Theory.Representation.BinaryPermutation.FiveTensorNormalizer
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# Scalar rigidity of the deleted tensor square

Contractions against dual vectors reduce each commuting tensor endomorphism
to the scalar commutant of the four-dimensional deleted core, first on one
factor and then on the other. Binary scalars make the invertible commutant
trivial. The same contractions prove tensor faithfulness and rule out an
identity exchange. Source: Aschbacher–Smith D.3.7, printed pp.197–199.
-/
public section
open scoped TensorProduct
open Representation
namespace BinaryPermutation.FiveTensorSquare
private def contractR (l : C →ₗ[ZMod 2] ZMod 2) : V →ₗ[ZMod 2] C :=
  (TensorProduct.rid (ZMod 2) C).toLinearMap.comp (l.lTensor C)
private def contractL (l : C →ₗ[ZMod 2] ZMod 2) : V →ₗ[ZMod 2] C :=
  (TensorProduct.lid (ZMod 2) C).toLinearMap.comp (l.rTensor C)
private theorem contractR_tmul (l : C →ₗ[ZMod 2] ZMod 2) (u v : C) :
    contractR l (u ⊗ₜ[ZMod 2] v) = l v • u := by simp [contractR]
private theorem contractL_tmul (l : C →ₗ[ZMod 2] ZMod 2) (u v : C) :
    contractL l (u ⊗ₜ[ZMod 2] v) = l u • v := by simp [contractL]
private theorem contract_comm (l r : C →ₗ[ZMod 2] ZMod 2) (x : V) :
    l (contractR r x) = r (contractL l x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp [contractR_tmul, contractL_tmul, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]
private theorem contractR_left (l : C →ₗ[ZMod 2] ZMod 2) (g : Alt) (x : V) :
    contractR l (deletedAction (g,1) x) = δ g (contractR l x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    change contractR l (δ g u ⊗ₜ[ZMod 2] δ 1 v) = _
    simp [contractR_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
private theorem contractL_right (l : C →ₗ[ZMod 2] ZMod 2) (g : Alt) (x : V) :
    contractL l (deletedAction (1,g) x) = δ g (contractL l x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    change contractL l (δ 1 u ⊗ₜ[ZMod 2] δ g v) = _
    simp [contractL_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
private theorem contractR_ext {x y : V}
    (h : ∀ l : C →ₗ[ZMod 2] ZMod 2, contractR l x = contractR l y) : x = y := by
  let b := Module.finBasis (ZMod 2) C
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  apply Finsupp.ext
  intro i
  simpa only [TensorProduct.equivFinsuppOfBasisRight_apply, contractR,
    LinearMap.comp_apply, LinearEquiv.coe_coe] using h (b.coord i)

theorem deleted_commuting_scalar (f : V →ₗ[ZMod 2] V)
    (hf : ∀ (g : Alt × Alt) v, f (deletedAction g v) = deletedAction g (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  have hdim : Module.finrank (ZMod 2) C = 4 := by
    rw [finrank_core, Fintype.card_fin]
  let : Nontrivial C := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) C)
  obtain ⟨z, hz⟩ := exists_ne (0 : C)
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hz
  let t : C →ₗ[ZMod 2] C := (contractL l).comp (f.comp (TensorProduct.mk (ZMod 2) C C z))
  have hright (g : Alt) (v : C) : t (δ g v) = δ g (t v) := by
    change contractL l (f (z ⊗ₜ[ZMod 2] δ g v)) = _
    have he : z ⊗ₜ[ZMod 2] δ g v = deletedAction (1,g) (z ⊗ₜ[ZMod 2] v) := by
      change _ = δ 1 z ⊗ₜ[ZMod 2] δ g v
      simp
    rw [he, hf, contractL_right]
    rfl
  obtain ⟨c, hc⟩ := FiveTensorNormalizer.core_commuting_scalar t hright
  refine ⟨c, ?_⟩
  have htensor (u v : C) : f (u ⊗ₜ[ZMod 2] v) = u ⊗ₜ[ZMod 2] t v := by
    apply contractR_ext
    intro r
    let F : C →ₗ[ZMod 2] C :=
      (contractR r).comp (f.comp ((TensorProduct.mk (ZMod 2) C C).flip v))
    have hF (g : Alt) (u : C) : F (δ g u) = δ g (F u) := by
      change contractR r (f (δ g u ⊗ₜ[ZMod 2] v)) = _
      have he : δ g u ⊗ₜ[ZMod 2] v = deletedAction (g,1) (u ⊗ₜ[ZMod 2] v) := by
        change _ = δ g u ⊗ₜ[ZMod 2] δ 1 v
        simp
      rw [he, hf, contractR_left]
      rfl
    obtain ⟨a, ha⟩ := FiveTensorNormalizer.core_commuting_scalar F hF
    have hat : a = r (t v) := by
      have hh := congrArg l (ha z)
      change l (contractR r (f (z ⊗ₜ[ZMod 2] v))) = l (a • z) at hh
      rw [contract_comm, map_smul, hl, smul_eq_mul, mul_one] at hh
      exact hh.symm
    change F u = contractR r (u ⊗ₜ[ZMod 2] t v)
    rw [ha, contractR_tmul, hat]
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => rw [htensor, hc, TensorProduct.tmul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- The invertible centralizer of the deleted tensor square is trivial. -/
theorem deleted_centralizer (f : V ≃ₗ[ZMod 2] V)
    (hf : ∀ (g : Alt × Alt) v, f (deletedAction g v) = deletedAction g (f v)) :
    f = LinearEquiv.refl (ZMod 2) V := by
  obtain ⟨c,hc⟩ := deleted_commuting_scalar f.toLinearMap hf
  have hbinary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hbinary c with h0 | h1
  · have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [finrank_V]; decide)
    obtain ⟨v,hv⟩ := exists_ne (0 : V)
    have he : f v = f 0 := by simpa only [h0,zero_smul,LinearEquiv.coe_coe,map_zero] using hc v
    exact (hv (f.injective he)).elim
  · apply LinearEquiv.ext
    intro v
    simpa [h1] using hc v

private theorem core_nontrivial : Nontrivial C :=
  Module.nontrivial_of_finrank_pos (by rw [finrank_core]; decide)

/-- Over the binary field, an identity tensor of two invertible maps has
identity factors. -/
theorem tensor_identity_factors (a b : C ≃ₗ[ZMod 2] C)
    (h : ∀ u v, a u ⊗ₜ[ZMod 2] b v = u ⊗ₜ[ZMod 2] v) :
    a = LinearEquiv.refl (ZMod 2) C ∧ b = LinearEquiv.refl (ZMod 2) C := by
  let := core_nontrivial
  obtain ⟨z,hz⟩ := exists_ne (0 : C)
  have hbz : b z ≠ 0 := fun h => hz (b.injective (h.trans (map_zero b).symm))
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hbz
  have ha (u : C) : a u = l z • u := by
    have hh := congrArg (contractR l) (h u z)
    simpa only [contractR_tmul,hl,one_smul] using hh
  have hbinary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hlz : l z = 1 := by
    rcases hbinary (l z) with h0 | h1
    · exact (hz (a.injective (by simpa only [h0,zero_smul,map_zero] using ha z))).elim
    · exact h1
  have ha1 : a = LinearEquiv.refl (ZMod 2) C := by
    apply LinearEquiv.ext
    intro u
    simpa only [hlz,one_smul,LinearEquiv.refl_apply] using ha u
  refine ⟨ha1, ?_⟩
  obtain ⟨r,hr⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hz
  apply LinearEquiv.ext
  intro v
  have hh := congrArg (contractL r) (h z v)
  simpa only [ha1,LinearEquiv.refl_apply,contractL_tmul,hr,one_smul] using hh

/-- A coordinate exchange cannot act as the identity on a four-dimensional
factor tensor square. -/
theorem tensor_exchange_ne_identity (a b : C ≃ₗ[ZMod 2] C) :
    ¬ (∀ u v, a v ⊗ₜ[ZMod 2] b u = u ⊗ₜ[ZMod 2] v) := by
  intro h
  let := core_nontrivial
  obtain ⟨z,hz⟩ := exists_ne (0 : C)
  have hbz : b z ≠ 0 := fun h => hz (b.injective (h.trans (map_zero b).symm))
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hbz
  have ha (v : C) : a v = l v • z := by
    have hh := congrArg (contractR l) (h z v)
    simpa only [contractR_tmul,hl,one_smul] using hh
  have hi : Function.Injective l := by
    intro u v huv
    apply a.injective
    rw [ha,ha,huv]
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  rw [finrank_core,Module.finrank_self,Fintype.card_fin] at hd
  omega
end BinaryPermutation.FiveTensorSquare
