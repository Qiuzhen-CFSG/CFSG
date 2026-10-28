module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.StrictComponent
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.ActionAdapter

/-!
# The prescribed orthogonal action gives a strict overcomponent

This applies the strict-component theorem to the exact centralizer quotient
and subrepresentation furnished by SourceA5FixedCenterOrthogonalAction.
Equivariance discharges both point-stabilizer identifications. Only the
preceding original layer-vector markings remain explicit.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_a5_fixed_center_strict_component_of_coordinates
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {H : Subgroup G} (hH : H∈Chapter3.HStar (T:Subgroup G) D.maximalLocal)
    (hHN : H≤normalizer (ChapterB.baumann (T:Subgroup G):Set G))
    (hred : IsPReduced 2 ((conjugateSpanBy
      (omegaOneCenterAmbient (T:Subgroup G)) H).subgroupOf H)) :
    let W := conjugateSpanBy (omegaOneCenterAmbient (T:Subgroup G)) H
    letI := hred.normal
    letI := hred.elementary
    ∀ (S : Subrepresentation (centralizerQuotient (W.subgroupOf H)))
      (c : S.toSubmodule ≃ₗ[ZMod 2] BinaryFourPlus.V)
      (ew : (H ⧸ centralizer (W.subgroupOf H : Set H)) ≃* BinaryFourPlus.Wreath),
      (∀ x v, c (S.toRepresentation x v) =
        (BinaryFourPlus.wreathToIsometry (ew x)).val (c v)) →
      ∀ (u₁ u₂ : S.toSubmodule) (a b : BinaryFourPlus.Plane),
      a≠0 → b≠0 → c u₁=(a,0) → c u₂=(0,b) →
      let v₁ : G := (u₁.val.toMul : H)
      let v₂ : G := (u₂.val.toMul : H)
      ∀ t : G,
      v₁∈(blockU L).map L.subtype →
      v₁∈centralizer ((T:Subgroup G)⊓L:Set G) →
      t∈(T:Subgroup G) →
      v₂∈(blockU (L.map (MulAut.conj t).toMonoidHom)).map
        (L.map (MulAut.conj t).toMonoidHom).subtype →
      v₂∈(T:Subgroup G) → v₂≠1 → v₂∈centralizer (L:Set G) →
      (T:Subgroup G)⊓centralizer ({v₂}:Set G)=
        (T:Subgroup G)⊓normalizer (L:Set G) →
      ∃ I : Subgroup G, L<I ∧ I≤centralizer ({v₂}:Set G) ∧
        (I.subgroupOf (centralizer ({v₂}:Set G))).IsCComponent ∧
        centralizer ({v₂}:Set G)≤normalizer (I:Set G) := by
  let W := conjugateSpanBy (omegaOneCenterAmbient (T:Subgroup G)) H
  let := hred.normal
  let := hred.elementary
  dsimp only
  intro S c ew hw u₁ u₂ a b ha hb hc₁ hc₂ t hv₁L hv₁T ht hv₂ hv₂T hv₂ne hv₂L hCT
  let q := QuotientGroup.mk' (centralizer (W.subgroupOf H : Set H))
  let f := ew.toMonoidHom.comp q
  have hf : Function.Surjective f := ew.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfix₁ := fun h:H => orthogonal_ambient_action_fixed_iff H.subtype H.subtype_injective
    (W.subgroupOf H) S c ew hw h u₁
  have hfix₂ := fun h:H => orthogonal_ambient_action_fixed_iff H.subtype H.subtype_injective
    (W.subgroupOf H) S c ew hw h u₂
  simp only [hc₁] at hfix₁
  simp only [hc₂] at hfix₂
  exact source_a5_fixed_center_strict_containing_component D e hn hout hH hHN hred
    f hf _ _ t a b ha hb hfix₁ hfix₂ u₁.val.toMul.property
    hv₁L hv₁T ht hv₂ hv₂T hv₂ne hv₂L hCT

end CFSG.Quasithin.Chapter10
