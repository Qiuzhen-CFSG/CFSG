module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.ModeledPair
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CommutingCenters

/-!
# Literal original-vector coordinates and ambient point stabilizers

The prescribed original layer vectors are distinct displacement centers of
commuting rank-one actors on the exact moved module. The binary orthogonal
calculation places them on opposite coordinate planes. The identity or the
literal plane swap orients them while simultaneously conjugating the actor
marking. Equivariance identifies each model point stabilizer with the
centralizer of the prescribed original ambient vector.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_a5_original_pair_coordinates
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {t : G} (ht : t∈(T : Subgroup G)) (htn : t∉normalizer (L : Set G))
    (p : SourceA5OriginalFixedPair D t)
    (hgen : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hWE : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H ≤
      omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)))
    (hred : IsPReduced 2 ((conjugateSpanBy
      (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H)) :
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
    letI := hred.normal
    letI := hred.elementary
    ∀ (S : Subrepresentation (centralizerQuotient (W.subgroupOf H))),
      S.toSubmodule.toAddSubgroup.toSubgroup'.map
        (H.subtype.comp (W.subgroupOf H).subtype) = ⁅W,H⁆ →
      Function.Injective S.toRepresentation →
      ∀ (c : S.toSubmodule ≃ₗ[ZMod 2] BinaryFourPlus.V)
        (ew : (H ⧸ centralizer (W.subgroupOf H : Set H)) ≃* BinaryFourPlus.Wreath),
      (∀ x v, c (S.toRepresentation x v) =
        (BinaryFourPlus.wreathToIsometry (ew x)).val (c v)) →
      ∃ (c' : S.toSubmodule ≃ₗ[ZMod 2] BinaryFourPlus.V)
        (ew' : (H ⧸ centralizer (W.subgroupOf H : Set H)) ≃* BinaryFourPlus.Wreath),
        (∀ x v, c' (S.toRepresentation x v) =
          (BinaryFourPlus.wreathToIsometry (ew' x)).val (c' v)) ∧
        ∃ (u₁ u₂ : S.toSubmodule) (a b : BinaryFourPlus.Plane),
          a≠0 ∧ b≠0 ∧ c' u₁=(a,0) ∧ c' u₂=(0,b) ∧
          ((u₁.val.toMul : H) : G)=p.first ∧
          ((u₂.val.toMul : H) : G)=p.second ∧
          (∀ h:H, (BinaryFourPlus.wreathToIsometry
            (ew' (QuotientGroup.mk' (centralizer (W.subgroupOf H : Set H)) h))).val
              (a,0)=(a,0) ↔ (h:G)∈centralizer ({p.first} : Set G)) ∧
          (∀ h:H, (BinaryFourPlus.wreathToIsometry
            (ew' (QuotientGroup.mk' (centralizer (W.subgroupOf H : Set H)) h))).val
              (0,b)=(0,b) ↔ (h:G)∈centralizer ({p.second} : Set G)) := by
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  let := hred.normal
  let := hred.elementary
  dsimp only
  intro S hSA hfaith c ew hw
  obtain ⟨u₁,u₂,w₁,w₂,hu₁,hu₂,hn₁,hn₂,hne₁₂,hcomm,hl₁,hl₂,hm₁,hm₂⟩ :=
    source_a5_original_pair_model_centers D e hn hne hout ht htn p hgen
      hH hWE hred S hSA hfaith c ew hw
  obtain ⟨s,a,b,_,ha,hb,hc₁,hc₂⟩ :=
    BinaryFourPlus.exists_oriented_commuting_centers w₁ w₂ (c u₁) (c u₂)
      hcomm hn₁ hn₂ hne₁₂ hl₁ hl₂ hm₁ hm₂
  let c' := c.trans (BinaryFourPlus.wreathToIsometry s).val
  let ew' := ew.trans (MulAut.conj s)
  have hw' : ∀ x v, c' (S.toRepresentation x v) =
      (BinaryFourPlus.wreathToIsometry (ew' x)).val (c' v) := by
    intro x v
    change (BinaryFourPlus.wreathToIsometry s).val (c (S.toRepresentation x v)) = _
    rw [hw]
    exact (BinaryFourPlus.wreath_action_conj_apply s (ew x) (c v)).symm
  have hf₁ := fun h:H => orthogonal_ambient_action_fixed_iff H.subtype H.subtype_injective
    (W.subgroupOf H) S c' ew' hw' h u₁
  have hf₂ := fun h:H => orthogonal_ambient_action_fixed_iff H.subtype H.subtype_injective
    (W.subgroupOf H) S c' ew' hw' h u₂
  have hc₁' : c' u₁=(a,0) := hc₁
  have hc₂' : c' u₂=(0,b) := hc₂
  simp only [hc₁',Subgroup.subtype_apply,hu₁] at hf₁
  simp only [hc₂',Subgroup.subtype_apply,hu₂] at hf₂
  exact ⟨c',ew',hw',u₁,u₂,a,b,ha,hb,hc₁',hc₂',hu₁,hu₂,hf₁,hf₂⟩

end CFSG.Quasithin.Chapter10
