module
public import Theory.PGroupCore

/-!
# The range of a homomorphism with p-core kernel

If the kernel of a group homomorphism is exactly the p-core of its domain,
the p-core of its literal range is trivial. No finiteness assumption is
needed. The p-core of the range pulls back to a normal p-subgroup because
the kernel is a p-group; maximality puts the entire preimage in the kernel.

This standard p-core quotient property lets finite-action applications keep
their actual automorphism range instead of replacing the action by an
abstract isomorphic quotient. It is used in the Section One action attached
to Stellmacher (9.4), printed p.51 of `refs/files/stellmacher-n-group.pdf`.
-/

public theorem pCore_range_eq_bot_of_ker_eq_pCore
    {G H : Type*} [Group G] [Group H] (p : ℕ)
    (hom : G →* H) (hkernel : hom.ker = pCore p G) :
    pCore p hom.range = ⊥ := by
  let projection := hom.rangeRestrict
  have hker : projection.ker = pCore p G := (MonoidHom.ker_rangeRestrict hom).trans hkernel
  have hkerP : IsPGroup p projection.ker := by rw [hker]; exact pCore_isPGroup
  have hpreP : IsPGroup p ((pCore p hom.range).comap projection) :=
    pCore_isPGroup.comap_of_ker_isPGroup projection hkerP
  have hle : (pCore p hom.range).comap projection ≤ projection.ker := by
    rw [hker]
    exact le_sSup ⟨inferInstance, hpreP⟩
  apply bot_unique
  intro actor hactor
  obtain ⟨original, rfl⟩ := hom.rangeRestrict_surjective actor
  exact MonoidHom.mem_ker.mp (hle hactor)
