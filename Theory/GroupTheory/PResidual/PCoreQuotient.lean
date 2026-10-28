module

public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Residual core quotients through p-group kernels

A surjective homomorphism with p-group kernel identifies the quotients of
the two p-residuals by their intrinsic p-cores. Restrict the homomorphism
to the residual, use surjectivity of the residual image, and lift p-cores
through the restricted p-group kernel.

This is the quotient transport needed for the Held local calculation in
Aschbacher--Smith, printed p.526. It does not require identifying either
residual with a commutator subgroup or placing the whole kernel in it.
-/

namespace MonoidHom
open Subgroup

/-- A p-group kernel preserves the intrinsic core quotient of the p-residual. -/
public noncomputable def pResidualCoreQuotientEquiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hk : IsPGroup p f.ker) :
    (pResidual p G ⧸ pCore p (pResidual p G)) ≃*
      (pResidual p H ⧸ pCore p (pResidual p H)) := by
  let e := MulEquiv.subgroupCongr (map_pResidual_of_surjective p f hf)
  let g := e.toMonoidHom.comp (f.subgroupMap (pResidual p G))
  have hg : Function.Surjective g := e.surjective.comp (f.subgroupMap_surjective _)
  have he : g.ker = f.ker.subgroupOf (pResidual p G) := by
    dsimp only [g]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ker_subgroupMap]
  have hkg : IsPGroup p g.ker :=
    hk.comap_subtype.of_equiv (MulEquiv.subgroupCongr he.symm)
  exact g.pCoreQuotientEquiv hg hkg

end MonoidHom
