module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.RadicalSeed
public import Theory.GroupTheory.Amalgam.LocalStructure

/-!
# The orders and intrinsic transport of the first Hall--Janko factors

The literal centralizer has order 1920 by `Order`. The fixed outer word
centralizes its defining involution, hence normalizes this factor. It is an
involution outside the whole inner carrier, so adjoining it doubles the order
to 3840. The fixed inner Sylow lies in the centralizer; consequently this join
is exactly `Seed.l₁s`, with the source's full numerator.

The actual carrier inclusion identifies `Seed.l₁` with `Seed.outerL 0` and
transports their intrinsic two-cores and quotients. The remaining radical and
quotient calculations are not asserted by these equivalences.
Source: Aschbacher--Smith F.1.12(I)(10)--(11), printed p.263 (PDF p.274),
and the retained ATLAS J2G1-p100B0 permutation data.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
open Theory.GroupTheory GeneratorPair Seed

set_option maxRecDepth 100000 in
theorem outerElement_fixes_z : extensionAction outerElement z = z := by
  apply inclusion_injective
  change extension.subtype outerElement * inclusion z * (extension.subtype outerElement)⁻¹ =
    inclusion z
  have hz : inclusion z = FirstFusion.tPerm := FirstFusion.inclusion_t
  rw [SecondParabolic.outerElement_inclusion, hz]
  decide +kernel

set_option maxRecDepth 4000 in
theorem outerElement_normalizes_outerL :
    outerElement ∈ Subgroup.normalizer (outerL 0 : Set Extension) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hle : (outerL 0).map (MulAut.conj outerElement).toMonoidHom ≤ outerL 0 := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨extensionAction outerElement g, ?_, ?_⟩
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      have h := congrArg (extensionAction outerElement)
        (Subgroup.mem_centralizer_singleton_iff.mp hg)
      simpa only [map_mul, outerElement_fixes_z] using h
    · apply extension.subtype_injective
      rfl
  apply le_antisymm hle
  intro x hx
  refine Subgroup.mem_map.mpr ⟨(MulAut.conj outerElement) x,
    hle (Subgroup.mem_map_of_mem _ hx), ?_⟩
  change outerElement * (outerElement * x * outerElement⁻¹) * outerElement⁻¹ = x
  have ht : outerElement * outerElement = 1 := by
    simpa only [pow_two] using SecondParabolic.outerElement_sq
  have hi : outerElement⁻¹ = outerElement := inv_eq_of_mul_eq_one_left ht
  rw [hi]
  simp only [← mul_assoc, one_mul, mul_assoc x, ht, mul_one]

theorem l₁s_eq_sup_outerElement : l₁s = outerL 0 ⊔ Subgroup.zpowers outerElement := by
  have hs : s.map intoExtension ≤ outerL 0 := Subgroup.map_mono SecondParabolic.s_le_l₁
  rw [l₁s, outerS, ← sup_assoc, sup_eq_left.mpr hs]

noncomputable def firstFactorEquiv : l₁ ≃* outerL 0 :=
  Subgroup.equivMapOfInjective l₁ intoExtension SecondParabolic.intoExtension_injective

noncomputable def firstCoreEquiv : pCore 2 l₁ ≃* pCore 2 (outerL 0) :=
  LocalCoreTransport.coreEquiv 2 firstFactorEquiv

noncomputable def firstQuotientEquiv :
    (l₁ ⧸ pCore 2 l₁) ≃* (outerL 0 ⧸ pCore 2 (outerL 0)) :=
  LocalCoreTransport.quotientEquiv 2 firstFactorEquiv

theorem card_outerL : Nat.card (outerL 0) = 1920 :=
  (Nat.card_congr firstFactorEquiv.symm.toEquiv).trans card_l₁

theorem card_l₁s : Nat.card l₁s = 3840 := by
  rw [l₁s_eq_sup_outerElement]
  have hout : outerElement ∉ outerL 0 := fun h =>
    SecondParabolic.outerElement_not_mem_range ((L 0).map_le_range intoExtension h)
  have h := Subgroup.card_sup_zpowers_of_normalizing_involution
    (outerL 0) outerElement SecondParabolic.outerElement_sq hout outerElement_normalizes_outerL
  rw [card_outerL] at h
  exact h

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
