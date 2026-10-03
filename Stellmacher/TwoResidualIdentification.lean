module

public import Stellmacher.SectionsOneToFourDefs
public import BenderSuzuki.External.Huppert.IV.Residual

/-!
# The internal two-residual in quotient notation

Stellmacher's internal two-residual is the intersection of normal subgroups of
2-power index. For finite groups, quotient cardinality is the subgroup index,
so this equals Huppert's intersection of normal subgroups with 2-group quotient.

This small conversion module preserves the public declaration originally
proved in the primitive dihedral quotient construction. It supplies residual
notation adapters without importing that construction's mathematical results.
-/

namespace Stellmacher.SectionThree

universe u

public theorem twoResidualSubgroup_eq_hktPResidual'
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    twoResidualSubgroup H = BenderSuzuki.External.hktPResidual 2 H := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRnormal : (BenderSuzuki.External.hktPResidual 2 H).Normal :=
    BenderSuzuki.External.hktPResidual_normal
  let _ : (BenderSuzuki.External.hktPResidual 2 H).Normal := hRnormal
  apply le_antisymm
  · rw [twoResidualSubgroup]
    apply sInf_le
    refine ⟨hRnormal, ?_⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp
      (BenderSuzuki.External.hktPResidual_quotient_isPGroup (q := 2) (Q := H))
    exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  · intro x hx
    rw [twoResidualSubgroup, Subgroup.mem_sInf]
    intro N hN
    let _ : N.Normal := hN.1
    apply BenderSuzuki.External.hktPResidual_le N hN.1 ?_ hx
    rw [IsPGroup.iff_card]
    obtain ⟨n, hn⟩ := hN.2
    exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩

end Stellmacher.SectionThree
