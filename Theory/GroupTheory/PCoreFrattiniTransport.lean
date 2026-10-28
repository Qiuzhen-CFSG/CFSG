module

public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.Frattini

/-!
# Frattini preimages above a prime core

A surjection with p-group kernel induces an isomorphism modulo the p-cores.
Frattini subgroups correspond under that isomorphism, so their full preimages
also correspond. This retains the Frattini factor in the notation O_{p,Φ}.

The proof first checks the kernel of the induced quotient map, then uses
Frattini functoriality in both directions of the resulting isomorphism.
Source application: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.41(2), printed p.1138; the O_{p,Φ} convention is on printed p.491.
-/

open Subgroup
@[expose] public section

namespace QuotientGroup
variable {G H : Type*} [Group G] [Group H]
/-- A surjection induces an isomorphism when the denominator is the exact preimage. -/
noncomputable def equivOfSurjectiveComap (f : G →* H) (hf : Function.Surjective f)
    (N : Subgroup G) (M : Subgroup H) [N.Normal] [M.Normal]
    (he : M.comap f = N) : G ⧸ N ≃* H ⧸ M := by
  let g := QuotientGroup.map N M f he.ge
  apply MulEquiv.ofBijective g
  refine ⟨?_, QuotientGroup.map_surjective_of_surjective N M f
    ((QuotientGroup.mk'_surjective M).comp hf) he.ge⟩
  apply (MonoidHom.ker_eq_bot_iff g).mp
  rw [QuotientGroup.ker_map, he, QuotientGroup.map_mk'_self]
end QuotientGroup

namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
  {p : ℕ} [Fact p.Prime]
/-- Removing a p-group kernel does not change the quotient by the p-core. -/
noncomputable def pCoreQuotientEquiv (f : G →* H) (hf : Function.Surjective f)
    (hk : IsPGroup p f.ker) : G ⧸ pCore p G ≃* H ⧸ pCore p H :=
  QuotientGroup.equivOfSurjectiveComap f hf _ _ (f.comap_pCore_of_ker_isPGroup hf hk)

/-- The Frattini preimage above the p-core is preserved by p-group kernels. -/
theorem comap_frattini_pCore_of_pKernel (f : G →* H) (hf : Function.Surjective f)
    (hk : IsPGroup p f.ker) :
    ((frattini (H ⧸ pCore p H)).comap (QuotientGroup.mk' (pCore p H))).comap f =
      (frattini (G ⧸ pCore p G)).comap (QuotientGroup.mk' (pCore p G)) := by
  let e := f.pCoreQuotientEquiv hf hk
  have he : (frattini (H ⧸ pCore p H)).comap e.toMonoidHom =
      frattini (G ⧸ pCore p G) := by
    apply le_antisymm
    · intro x hx
      have ht := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective hx
      simpa using ht
    · exact frattini_le_comap_frattini_of_surjective e.surjective
  have hcomp : e.toMonoidHom.comp (QuotientGroup.mk' (pCore p G)) =
      (QuotientGroup.mk' (pCore p H)).comp f := by
    ext x
    rfl
  rw [← he, Subgroup.comap_comap, Subgroup.comap_comap, hcomp]
end MonoidHom

end
