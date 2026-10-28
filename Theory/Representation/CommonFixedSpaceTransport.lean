module

public import Theory.Representation.ScalarDescent
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Transport of common fixed spaces of two operators

A product of the two displacement maps expresses their common fixed space
as one kernel. Flat scalar extension and actual intertwining equivalences
therefore preserve its dimension. These general lemmas are adapted from
`OuterSchurDegree.FixedSpace.Transport` in the completed symplectic K.3.4
calculation (fleet attempt 64431f55976340f083f01c48a790299a), with the original
proofs retained there. They also supply the literal Schur-normalizer operators
used by the SL₃ outer tensor calculation in K.3.2.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5.
-/

@[expose] public section
open scoped TensorProduct
open Module
namespace LinearMap.FixedSpaceTransport
section Linear
variable {F E W X : Type*} [Field F] [Field E] [Algebra F E]
  [AddCommGroup W] [Module F W]
  [AddCommGroup X] [Module F X]

/-- Field extension preserves the dimension of a kernel. -/
theorem finrank_ker_baseChange (f : W →ₗ[F] X) :
    finrank E (f.baseChange E).ker = finrank F f.ker := by
  rw [← (LinearMap.kerBaseChangeEquiv (E := E) f).finrank_eq]
  exact Module.finrank_baseChange

/-- Field extension preserves the intersection of two kernel equations. -/
theorem finrank_inf_ker_baseChange (f g : Module.End F W) :
    finrank E ↥((f.baseChange E).ker ⊓ (g.baseChange E).ker) =
      finrank F ↥(f.ker ⊓ g.ker) := by
  have h : (TensorProduct.prodRight F E E W W).toLinearMap.comp
      ((f.prod g).baseChange E) = (f.baseChange E).prod (g.baseChange E) := by
    ext a <;> simp
  rw [← LinearMap.ker_prod, ← h, LinearEquiv.ker_comp,
    finrank_ker_baseChange, LinearMap.ker_prod]

/-- Scalar extension preserves the common fixed dimension of two operators. -/
theorem finrank_commonFixed_baseChange (f g : Module.End F W) :
    finrank E ↥((f.baseChange E - 1).ker ⊓ (g.baseChange E - 1).ker) =
      finrank F ↥((f - 1).ker ⊓ (g - 1).ker) := by
  have h := finrank_inf_ker_baseChange (E := E) (f - 1) (g - 1)
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_sub,
    LinearMap.baseChange_one] at h
  exact h

theorem finrank_inf_self (S : Submodule F W) :
    finrank F ↥(S ⊓ S) = finrank F S := by rw [inf_idem]

/-- An actual intertwining equivalence transports both fixed equations. -/
noncomputable def commonFixedEquiv (e : W ≃ₗ[F] X)
    (f g : Module.End F W) (f' g' : Module.End F X)
    (hf : ∀ v, e (f v) = f' (e v)) (hg : ∀ v, e (g v) = g' (e v)) :
    ↥((f - 1).ker ⊓ (g - 1).ker) ≃ₗ[F] ↥((f' - 1).ker ⊓ (g' - 1).ker) := by
  have h : ((f' - 1).ker ⊓ (g' - 1).ker).comap e.toLinearMap =
      (f - 1).ker ⊓ (g - 1).ker := by
    ext v
    simp only [Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker,
      LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe,
      sub_eq_zero, ← hf, ← hg, e.injective.eq_iff]
  exact (LinearEquiv.ofEq _ _ h.symm).trans (e.ofSubmodule' _)

/-- An intertwining equivalence preserves the moved dimension. -/
theorem finrank_range_sub_one_equiv [FiniteDimensional F W] [FiniteDimensional F X]
    (e : W ≃ₗ[F] X)
    (f : Module.End F W) (f' : Module.End F X)
    (hf : ∀ v, e (f v) = f' (e v)) :
    finrank F (f - 1).range = finrank F (f' - 1).range := by
  have hk := (commonFixedEquiv e f f f' f' hf hf).finrank_eq
  rw [finrank_inf_self, finrank_inf_self] at hk
  have hW := (f - 1).finrank_range_add_finrank_ker
  have hX := (f' - 1).finrank_range_add_finrank_ker
  have he := e.finrank_eq
  omega
end Linear
end LinearMap.FixedSpaceTransport
