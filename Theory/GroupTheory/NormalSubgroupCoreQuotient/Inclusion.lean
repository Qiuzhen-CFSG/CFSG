module
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
The normal-subgroup core-quotient kernel identity along a literal inclusion
of ambient subgroups. Transport through `subgroupOfEquivOfLe` identifies the
intrinsic core without replacing the source's quotient map. The original
end-node quotient XS → XT/O₂(XT) in [AS, 15.3.25] uses this form.
-/

public noncomputable section
namespace Subgroup
variable {G : Type*} [Group G] (p : ℕ) {J K : Subgroup G} (hJK : J ≤ K)
    [(J.subgroupOf K).Normal]
/-- Restrict the ambient core quotient along the literal inclusion of nested groups. -/
theorem ker_coreQuotient_inclusion :
    ((QuotientGroup.mk' (pCore p K)).comp (inclusion hJK)).ker = pCore p J := by
  let e : J ≃* J.subgroupOf K := (subgroupOfEquivOfLe hJK).symm
  have he : inclusion hJK = (J.subgroupOf K).subtype.comp e.toMonoidHom := rfl
  rw [he,←MonoidHom.comp_assoc,←MonoidHom.comap_ker,ker_coreQuotient_restrict]
  rw [←pCore_map_iso p e,comap_map_eq_self_of_injective e.injective]
end Subgroup
