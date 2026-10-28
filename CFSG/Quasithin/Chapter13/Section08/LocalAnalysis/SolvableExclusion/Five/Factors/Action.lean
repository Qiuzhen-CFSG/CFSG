module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.FactorData

/-!
# Faithfulness and the actual five-primary star image

The kernel of the H-action on UH/V₁, embedded back into G, is exactly
C_H(UH/V₁), expressed by the relative commutator preimage. Consequently
the source identity Q_H = C_H(UH/V₁) both constructs the action of H/Q_H
and proves its faithfulness. The conjugation formula uniquely determines
this action. For UH = ⟨V₃^H⟩ its normalization is automatic.

A five-subgroup P of H intersects the two-core trivially. Restricting the
quotient map therefore gives a specified isomorphism P ≃ P*, with its
pointwise formula; this permits later factors to be transported back into
the supplied P rather than into an unrelated abstract five-group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the standing
setup on printed p.946 and the five-primary paragraph of 13.8.13 on p.951.
The factor construction and rank-one conclusion are not asserted here.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
variable {G : Type*} [Group G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]

theorem StarAction.kernel_le (a : StarAction H UH V₁) :
    ((a.action.comp (QuotientGroup.mk' (pCore 2 H))).ker).map H.subtype ≤
      commutatorPreimage H UH V₁ := by
  apply le_commutatorPreimage (map_subtype_le _)
  apply commutator_le.mpr
  rintro _ ⟨h, hh, rfl⟩ u hu
  have he := congrArg (fun f : MulAut (UH ⧸ V₁.subgroupOf UH) =>
    f (QuotientGroup.mk' (V₁.subgroupOf UH) ⟨u, hu⟩)) hh
  change a.action (QuotientGroup.mk' (pCore 2 H) h)
    (QuotientGroup.mk' (V₁.subgroupOf UH) ⟨u, hu⟩) =
      QuotientGroup.mk' (V₁.subgroupOf UH) ⟨u, hu⟩ at he
  rw [a.conjugation] at he
  have hd := QuotientGroup.eq_iff_div_mem.mp he
  change (h : G) * u * (h : G)⁻¹ / u ∈ V₁ at hd
  simpa only [commutatorElement_def, div_eq_mul_inv, coe_subtype] using hd

theorem StarAction.injective_of_kernel (a : StarAction H UH V₁)
    (hk : Source.QH H = commutatorPreimage H UH V₁) :
    Function.Injective a.action := by
  apply (MonoidHom.ker_eq_bot_iff a.action).mp
  apply bot_unique
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
  have hm : (h : G) ∈ Source.QH H := by
    rw [hk]
    apply a.kernel_le
    exact mem_map_of_mem H.subtype hx
  have hQ : (Source.QH H).subgroupOf H = pCore 2 H :=
    comap_map_eq_self_of_injective H.subtype_injective _
  have hm' : h ∈ pCore 2 H := by
    rw [← hQ]
    exact hm
  exact (QuotientGroup.eq_one_iff h).mpr hm'

theorem exists_faithful_starAction (H UH V₁ : Subgroup G)
    [(V₁.subgroupOf UH).Normal]
    (hn : H ≤ normalizer (UH : Set G))
    (hz : H ≤ normalizer (V₁ : Set G))
    (hk : Source.QH H = commutatorPreimage H UH V₁) :
    ∃ a : StarAction H UH V₁, Function.Injective a.action := by
  have hc : ⁅UH, Source.QH H⁆ ≤ V₁ := by
    rw [commutator_comm, hk]
    exact commutator_commutatorPreimage_le H UH V₁ hz
  obtain ⟨a⟩ := exists_starAction H UH V₁ hn hz hc
  exact ⟨a, a.injective_of_kernel hk⟩


theorem five_star_injective {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 5 P) :
    Function.Injective ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hPH)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hq : (inclusion hPH x) ∈ pCore 2 H := (QuotientGroup.eq_one_iff _).mp hx
  have hQ : (x : G) ∈ Source.QH H := mem_map_of_mem H.subtype hq
  have hd : Disjoint P (Source.QH H) :=
    hP.disjoint_of_coprime (isPGroup_pCoreIn 2 H) (by decide)
  apply Subtype.ext
  exact hd.le_bot ⟨x.property, hQ⟩

noncomputable def fiveStarEquiv {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 5 P) :
    P ≃* Source.starImage H P := by
  let q := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hPH)
  have hq : q.range = Source.starImage H P := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  exact (MonoidHom.ofInjective (five_star_injective hPH hP)).trans
    (MulEquiv.subgroupCongr hq)

theorem fiveStarEquiv_apply {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 5 P)
    (x : P) :
    (fiveStarEquiv hPH hP x : Source.Hstar H) =
      QuotientGroup.mk' (pCore 2 H) (inclusion hPH x) := rfl

theorem StarAction.kernel_eq (a : StarAction H UH V₁)
    (hz : H ≤ normalizer (V₁ : Set G)) :
    ((a.action.comp (QuotientGroup.mk' (pCore 2 H))).ker).map H.subtype =
      commutatorPreimage H UH V₁ := by
  refine le_antisymm a.kernel_le ?_
  have hc : ⁅UH, commutatorPreimage H UH V₁⁆ ≤ V₁ := by
    rw [commutator_comm]
    exact commutator_commutatorPreimage_le H UH V₁ hz
  have hk := quotient_conjugation_action_kills_commutator_layer H UH V₁
    (commutatorPreimage H UH V₁) inferInstance a.normalizes hc
    (a.action.comp (QuotientGroup.mk' (pCore 2 H))) a.conjugation
  intro x hx
  exact ⟨⟨x, commutatorPreimage_le H UH V₁ hx⟩, hk hx, rfl⟩

theorem StarAction.action_eq (a b : StarAction H UH V₁) : a.action = b.action := by
  apply MonoidHom.ext
  intro x
  apply MulEquiv.ext
  intro w
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf UH) w
  rw [a.conjugation, b.conjugation]

theorem exists_faithful_source_starAction (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (hz : H ≤ normalizer (V₁ : Set G))
    (hk : Source.QH H = commutatorPreimage H (Source.UH H V₃) V₁) :
    ∃ a : StarAction H (Source.UH H V₃) V₁, Function.Injective a.action :=
  exists_faithful_starAction H (Source.UH H V₃) V₁
    (le_normalizer_conjugateSpanBy V₃ H) hz hk

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
