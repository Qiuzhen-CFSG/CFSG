module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.QuotientGeometry

/-!
# The actual two-member maximum elementary family of S/Φ(D)

The genuine quotient has elementary self-centralizing core, its elementary
conjugate of equal order, and the uniform full fixed-subgroup profile.
Counting and B.2.21 therefore give precisely the two literal core images.
No assertion about the family or its orbit is assumed.

Source: Aschbacher–Smith C.5.6(5), printed p.157.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]
variable {T : Type*} [Group T] [Finite T]

/-- The exact family for any realization of the actual quotient map. -/
theorem Setup.quotient_maximum_family (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (f : S R →* T) (hf : Function.Surjective f)
    (hk : f.ker = (Phi R L).subgroupOf (S R)) :
    elementaryAbelianMaxSubgroups (⊤ : Subgroup T) =
      {baumannImage R f (Q R L),
        baumannImage R f ((Q R L).map (MulAut.conj x⁻¹).toMonoidHom)} := by
  let := h.quotient_core_elementary hx hnc f hk
  let := h.quotient_opposite_elementary hx hnc f hk
  have hn : ((Q R L).subgroupOf (S R)).Normal :=
    normal_subgroupOf_of_le_normalizer (S_normalizes_Q R L)
  let : (baumannImage R f (Q R L)).Normal := hn.map f hf
  exact family_pair _ _ (h.quotient_core_selfcentralizing hx hnc f hf hk)
    (h.quotient_span hx hnc f hf) (h.quotient_opposite_not_le hx hnc f hk)
    (h.quotient_fixed_singleton hx hnc f hf hk) (h.quotient_core_card hx hnc f hk)

/-- C.5.6(5)'s two-member family on the literal S/Φ(D). -/
theorem Setup.frattini_quotient_family (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    let := h.phi_normal hx hnc
    let f := QuotientGroup.mk' ((Phi R L).subgroupOf (S R))
    elementaryAbelianMaxSubgroups (⊤ : Subgroup ((S R) ⧸ (Phi R L).subgroupOf (S R))) =
      {baumannImage R f (Q R L),
        baumannImage R f ((Q R L).map (MulAut.conj x⁻¹).toMonoidHom)} := by
  let := h.phi_normal hx hnc
  exact h.quotient_maximum_family hx hnc _ (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
