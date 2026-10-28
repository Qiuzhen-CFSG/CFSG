module

public import Theory.GroupTheory.PerfectCentralCoverEmbeddingRigidity

/-!
# Recovering a perfect group from its marked central quotient

An isomorphism L/Z(L) ≃ G specifies a perfect central cover of G whose
kernel is exactly Z(L). If the constructed universal projection onto G has
trivial kernel, the marked projection L → G is an isomorphism. The formula
for this isomorphism retains the given quotient map, rather than selecting
an unrelated identification of the groups.

Source: the universal-cover convention in Aschbacher–Smith I.1.1, printed
p.407, and the lifting argument in `PerfectCentralCoverEmbeddingRigidity`.
-/

public section

namespace PerfectCentralCovering

open Subgroup

variable {L G : Type*} [Group L] [Group G] [Group.IsPerfect L]

/-- The perfect central cover specified by a central-quotient isomorphism. -/
@[expose] def centralQuotientCover (e : L ⧸ center L ≃* G) : Cover L G where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

@[simp] theorem centralQuotientCover_apply (e : L ⧸ center L ≃* G) (x : L) :
    (centralQuotientCover e).toMonoidHom x = e (QuotientGroup.mk x) := rfl

/-- The kernel is the entire center, with the original quotient convention. -/
@[simp] theorem centralQuotientCover_ker (e : L ⧸ center L ≃* G) :
    (centralQuotientCover e).toMonoidHom.ker = center L := by
  change (e.toMonoidHom.comp (QuotientGroup.mk' _)).ker = _
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

/-- A trivial universal kernel kills the center of every perfect group
with the specified central quotient. -/
theorem center_eq_bot_of_centralQuotientEquiv
    (hm : (universalProjection G).ker = ⊥) (e : L ⧸ center L ≃* G) :
    center L = ⊥ := by
  rw [← centralQuotientCover_ker e]
  exact ((centralQuotientCover e).toMonoidHom.ker_eq_bot_iff).mpr
    ((centralQuotientCover e).injective_of_universalProjection_ker_eq_bot hm)

/-- Recover the original group using its literal marked central projection. -/
noncomputable def centralQuotientEquivOfUniversalKernelEqBot
    (hm : (universalProjection G).ker = ⊥) (e : L ⧸ center L ≃* G) : L ≃* G :=
  MulEquiv.ofBijective (centralQuotientCover e).toMonoidHom
    ⟨(centralQuotientCover e).injective_of_universalProjection_ker_eq_bot hm,
      (centralQuotientCover e).surjective⟩

@[simp] theorem centralQuotientEquivOfUniversalKernelEqBot_apply
    (hm : (universalProjection G).ker = ⊥) (e : L ⧸ center L ≃* G) (x : L) :
    centralQuotientEquivOfUniversalKernelEqBot hm e x = e (QuotientGroup.mk x) := by
  unfold centralQuotientEquivOfUniversalKernelEqBot
  rfl

end PerfectCentralCovering
