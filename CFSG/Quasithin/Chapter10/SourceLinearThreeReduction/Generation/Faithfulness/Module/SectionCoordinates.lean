module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.PairImage
public import Theory.Representation.BinaryConjugationSection

/-!
# Comparing the original moved quotient with a marked component section

When the opposite component centralizes the moved factor, its fixed kernel
for L equals its fixed kernel for the full orbit L₀. The first isomorphism
theorem identifies its image in V/C_V(L₀) with any marked section having
kernel C_[V,L](L). The comparison retains the original quotient projection
and the literal component action, including the complete central kernel.

Source: Aschbacher--Smith 10.1.1 and 10.2.3(2), printed pp.741 and 745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Projection of the original moved subgroup into the full central quotient. -/
def sourceMovedQuotientProjection : (⁅D.fullModule,L⁆ : Subgroup G) →* sourceMovedQuotient D L :=
  (MulEquiv.subgroupCongr (sourceMovedQuotient_eq D L).symm).toMonoidHom.comp
    (((QuotientGroup.mk' D.fullCentralizer).subgroupMap _).comp
      (subgroupOfEquivOfLe (le_normalizer_iff_commutator_le_left.mp
        (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
          D.maximalLocal_normalizes_fullModule))).symm.toMonoidHom)

/-- The comparison uses the original quotient map on each element. -/
theorem sourceMovedQuotientProjection_apply (w : (⁅D.fullModule,L⁆ : Subgroup G)) :
    (sourceMovedQuotientProjection D w : D.fullCentralQuotient) =
      QuotientGroup.mk' D.fullCentralizer
        ⟨w,le_normalizer_iff_commutator_le_left.mp
          (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
            D.maximalLocal_normalizes_fullModule) w.property⟩ := by rfl

/-- Every moved-quotient element lifts to the original moved subgroup. -/
theorem sourceMovedQuotientProjection_surjective : Function.Surjective (sourceMovedQuotientProjection D) :=
  (MulEquiv.subgroupCongr (sourceMovedQuotient_eq D L).symm).surjective.comp
    (((QuotientGroup.mk' D.fullCentralizer).subgroupMap_surjective _).comp
      (subgroupOfEquivOfLe _).symm.surjective)

/-- Opposite-component centralization identifies the two section kernels,
with equivariance for the literal component action. -/
theorem source_moved_quotient_coordinates_of_separated_section
    {t : G} (hpair : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom)
    (hsep : ⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G))
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) L V)
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) ρ) :
    ∃ e : sourceMovedQuotient D L ≃* Multiplicative V,
      (∀ w, e (sourceMovedQuotientProjection D w) = c.coordinates w) ∧
      ∀ k v, (e (sourceMovedQuotientAction D L L L.le_normalizer k v)).toAdd =
        ρ ⟨k.val.val,k.property⟩ (e v).toAdd := by
  let q := sourceMovedQuotientProjection D
  have hq : Function.Surjective q := sourceMovedQuotientProjection_surjective D
  have hk : q.ker = c.coordinates.ker := by
    ext w
    change q w = 1 ↔ c.coordinates w = 1
    rw [c.coordinates_eq_one_iff]
    have hh : q w = 1 ↔ (q w : D.fullCentralQuotient) = 1 := Subtype.val_inj.symm
    rw [hh,sourceMovedQuotientProjection_apply]
    constructor
    · intro hw
      have hc : (w : G) ∈ centralizer (localOrbit T L : Set G) :=
        (QuotientGroup.eq_one_iff (N := D.fullCentralizer) _).mp hw
      exact ⟨w.property,centralizer_le (le_componentOrbit L T) hc⟩
    · intro hw
      apply (QuotientGroup.eq_one_iff (N := D.fullCentralizer) _).mpr
      have hc : localOrbit T L ≤ centralizer ({(w : G)} : Set G) := by
        rw [hpair]
        exact sup_le
          (fun l hl => mem_centralizer_singleton_iff.mpr (hw.2 l hl))
          (fun l hl => mem_centralizer_singleton_iff.mpr (hsep w.property l hl))
      exact fun l hl => mem_centralizer_singleton_iff.mp (hc hl)
  let e : sourceMovedQuotient D L ≃* Multiplicative V :=
    (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivOfSurjective c.coordinates c.onto))
  have he (w : (⁅D.fullModule,L⁆ : Subgroup G)) : e (q w) = c.coordinates w := by
    change e ((QuotientGroup.quotientKerEquivOfSurjective q hq)
      (QuotientGroup.mk' q.ker w)) = _
    simp only [e,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
    rfl
  refine ⟨e,he,?_⟩
  intro k v
  obtain ⟨w,rfl⟩ := hq v
  let l : L := ⟨k.val.val,k.property⟩
  let w' : (⁅D.fullModule,L⁆ : Subgroup G) := ⟨(l : G) * (w : G) * (l : G)⁻¹,
    (mem_normalizer_iff.mp (c.normalized l.property) w).mp w.property⟩
  have ha : sourceMovedQuotientAction D L L L.le_normalizer k (q w) = q w' := by
    apply Subtype.ext
    rw [sourceMovedQuotientAction_apply,sourceMovedQuotientProjection_apply,sourceFullModuleQuotientAction_apply,
      sourceMovedQuotientProjection_apply]
  rw [ha,he,he]
  exact c.equivariant l w

end CFSG.Quasithin.Chapter10
