module

public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Fixed Sylow subgroups under the central quotient action

The image of a fixed subgroup is contained in the fixed subgroup of the induced
quotient automorphism. Equality is not asserted. A Sylow subgroup fixed pointwise
maps onto a Sylow subgroup fixed pointwise in any model of the central quotient.

This is the quotient transport used in Aschbacher–Smith, *The Classification of
Quasithin Groups*, Lemma 16.1.6, printed p.1172. It applies to automorphisms of
arbitrary order, so passage to the quotient does not restrict that lemma to
involutions.
-/

public section

namespace MulAut
variable {G H : Type*} [Group G] [Group H]

/-- Only containment is automatic for fixed subgroups under the quotient map. -/
theorem map_fixedSubgroup_le_quotient_center (a : MulAut G) :
    a.fixedSubgroup.map (QuotientGroup.mk' (Subgroup.center G)) ≤
      ((Subgroup.center G).quotientAut a).fixedSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_fixedSubgroup, Subgroup.quotientAut_apply_mk,
    (mem_fixedSubgroup a x).mp hx]

/-- Pointwise fixation descends to the actual Sylow image in a central quotient. -/
theorem centralQuotientAction_exists_fixed_sylow [Finite G] [Finite H]
    (e : G ⧸ Subgroup.center G ≃* H) (a : MulAut G)
    (S : Sylow 2 G) (hS : ∀ x ∈ S, a x = x) :
    ∃ T : Sylow 2 H, ∀ y ∈ T, centralQuotientAction e a y = y := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  refine ⟨S.mapSurjective hf, ?_⟩
  intro y hy
  change y ∈ (S : Subgroup G).map f at hy
  obtain ⟨x, hx, rfl⟩ := hy
  change centralQuotientAction e a (e (QuotientGroup.mk' (Subgroup.center G) x)) =
    e (QuotientGroup.mk' (Subgroup.center G) x)
  rw [centralQuotientAction_apply, hS x hx]

end MulAut
