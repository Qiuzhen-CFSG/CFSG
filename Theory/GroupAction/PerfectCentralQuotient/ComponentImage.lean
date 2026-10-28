module

public import Theory.GroupTheory.PerfectCentralQuotientNormalizer
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic

/-!
# Transporting a component to the full quotient fixed subgroup

The preimage of the quotient fixed subgroup normalizes the fixed subgroup
upstairs: the displacement of each preimage element is central, so its inner
automorphism commutes with the given action. Thus the upstairs fixed subgroup
is normal in that preimage. Subnormal ascent and surjective component transport
then place the component image in the full fixed subgroup downstairs. Its
image is nontrivial because a perfect subgroup in a central kernel is trivial.

This supplies the component transport for the centralizer-table deductions
in Aschbacher–Smith, 16.3.11(3), printed p.1181.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
namespace MulAut
variable {K : Type*} [Group K]

/-- The full preimage of quotient fixed points normalizes the upstairs fixed subgroup. -/
theorem quotient_fixed_preimage_le_normalizer_fixed (a : MulAut K) :
    (((center K).quotientAut a).fixedSubgroup).comap (QuotientGroup.mk' (center K)) ≤
      normalizer (a.fixedSubgroup : Set K) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  rw [mem_fixedSubgroup, map_mul, map_mul, map_inv,
    (mem_fixedSubgroup a x).mp hx]
  have hgq : QuotientGroup.mk' (center K) (a g) = QuotientGroup.mk' (center K) g := by
    have hh := (mem_fixedSubgroup ((center K).quotientAut a) _).mp hg
    rwa [quotientAut_apply_mk] at hh
  exact DFunLike.congr_fun (conj_eq_of_quotient_eq hgq) x

/-- Components of fixed subgroups have nontrivial component image in the full
fixed subgroup of the central quotient. -/
theorem component_image_in_quotient_fixed (a : MulAut K) (L : Subgroup K) (hL : IsComponentIn L a.fixedSubgroup) :
    IsComponentIn (L.map (QuotientGroup.mk' (center K)))
      ((center K).quotientAut a).fixedSubgroup := by
  let q := QuotientGroup.mk' (center K)
  let b := (center K).quotientAut a
  let P := b.fixedSubgroup.comap q
  have hCP : a.fixedSubgroup ≤ P := by
    intro x hx
    change q x ∈ b.fixedSubgroup
    rw [mem_fixedSubgroup, quotientAut_apply_mk, (mem_fixedSubgroup a x).mp hx]
  have hPN : P ≤ normalizer (a.fixedSubgroup : Set K) :=
    quotient_fixed_preimage_le_normalizer_fixed a
  have hLP := hL.of_subnormal hCP
    ((normal_subgroupOf_iff_le_normalizer hCP).mpr hPN).isSubnormal
  let f := q.subgroupComap b.fixedSubgroup
  have hf : Function.Surjective f := q.subgroupComap_surjective_of_surjective _
    (QuotientGroup.mk'_surjective _)
  have hLe : L.map q ≤ b.fixedSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    exact hCP (hL.1 hx)
  have hmap : (L.subgroupOf P).map f = (L.map q).subgroupOf b.fixedSubgroup := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_map_of_mem q hy
    · rintro ⟨y, hy, he⟩
      exact ⟨⟨y, hLP.1 hy⟩, hy, Subtype.ext he⟩
  refine ⟨hLe, ?_⟩
  rcases hLP.2.map_surjective f hf with hb | hc
  · exfalso
    have hLb : L.map q = ⊥ := by
      have hh := congrArg (Subgroup.map b.fixedSubgroup.subtype) hb
      rw [hmap, map_subgroupOf_eq_of_le hLe, Subgroup.map_bot] at hh
      exact hh
    let := hL.quasisimple
    have hLL : L ≤ (⊥ : Subgroup K) := perfect_le_of_map_le_of_central_kernel q
      (by rw [QuotientGroup.ker_mk']) L ⊥ (by rw [hLb, Subgroup.map_bot])
    exact hL.ne_bot (le_bot_iff.mp hLL)
  · exact hmap ▸ hc
end MulAut
