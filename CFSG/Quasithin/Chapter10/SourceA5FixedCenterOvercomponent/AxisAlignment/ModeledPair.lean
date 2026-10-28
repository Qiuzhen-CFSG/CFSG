module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.Membership
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.RepresentedActors

/-!
# The prescribed original pair gives commuting orthogonal displacement centers

Lift the actual original vectors through the exact ambient image of the moved
subrepresentation. Their commuting original block actors descend through the
unchanged centralizer quotient. Faithfulness and equivariance transfer their
realized displacement lines to the supplied orthogonal coordinates.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_a5_original_pair_model_centers
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
      ∃ (u₁ u₂ : S.toSubmodule) (w₁ w₂ : BinaryFourPlus.Wreath),
        ((u₁.val.toMul : H) : G) = p.first ∧
        ((u₂.val.toMul : H) : G) = p.second ∧
        c u₁ ≠ 0 ∧ c u₂ ≠ 0 ∧ c u₁ ≠ c u₂ ∧ Commute w₁ w₂ ∧
        (∀ x, (BinaryFourPlus.wreathToIsometry w₁).val x-x=0 ∨
          (BinaryFourPlus.wreathToIsometry w₁).val x-x=c u₁) ∧
        (∀ x, (BinaryFourPlus.wreathToIsometry w₂).val x-x=0 ∨
          (BinaryFourPlus.wreathToIsometry w₂).val x-x=c u₂) ∧
        (∃ x, (BinaryFourPlus.wreathToIsometry w₁).val x-x=c u₁) ∧
        (∃ x, (BinaryFourPlus.wreathToIsometry w₂).val x-x=c u₂) := by
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  let U := W.subgroupOf H
  let := hred.normal
  let := hred.elementary
  dsimp only
  intro S hSA hfaith c ew hw
  obtain ⟨_,_,hv₁,hv₂,hne₁₂,g₁,g₂,hg₁,hg₂,hcomm,hline₁,hline₂,hmove₁,hmove₂⟩ :=
    source_a5_original_pair_displacements D e hn hne hout ht htn p hgen H hH hWE
  have lift (v : G) (hv : v∈⁅W,H⁆) : ∃ u : S.toSubmodule, ((u.val.toMul:H):G)=v := by
    rw [←hSA] at hv
    obtain ⟨u,hu,he⟩ := hv
    exact ⟨⟨Additive.ofMul u,hu⟩,he⟩
  obtain ⟨u₁,hu₁⟩ := lift p.first hv₁
  obtain ⟨u₂,hu₂⟩ := lift p.second hv₂
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let g₁H : H := ⟨g₁,hH.1.1.2 hg₁.1⟩
  let g₂H : H := ⟨g₂,hH.1.1.2 hg₂.1⟩
  have transfer (g : G) (hg : g∈H) (v : G) (hv : v≠1)
      (u : S.toSubmodule) (hu : ((u.val.toMul:H):G)=v)
      (hl : ∀ x∈W, ⁅g,x⁆=1 ∨ ⁅g,x⁆=v)
      (hm : ∃ x∈W, ⁅g,x⁆=v) :
      let w := ew (q ⟨g,hg⟩)
      c u≠0 ∧
        (∀ x, (BinaryFourPlus.wreathToIsometry w).val x-x=0 ∨
          (BinaryFourPlus.wreathToIsometry w).val x-x=c u) ∧
        ∃ x, (BinaryFourPlus.wreathToIsometry w).val x-x=c u := by
    apply orthogonal_displacement_center U S hfaith c ew hw ⟨g,hg⟩ u
    · intro he
      exact hv (hu.symm.trans (congrArg Subtype.val he))
    · intro x hx
      exact (hl x hx).imp (fun he => Subtype.ext he)
        (fun he => Subtype.ext (he.trans hu.symm))
    · obtain ⟨x,hx,he⟩ := hm
      have hxH : x∈H := hH.1.1.2
        (((mem_omegaOneCenterAmbient_iff _ _).mp (hWE hx)).1.1)
      exact ⟨⟨x,hxH⟩,hx,Subtype.ext (he.trans hu.symm)⟩
  have h₁ := transfer g₁ g₁H.property p.first p.first_ne u₁ hu₁ hline₁ hmove₁
  have h₂ := transfer g₂ g₂H.property p.second p.second_ne u₂ hu₂ hline₂ hmove₂
  refine ⟨u₁,u₂,ew (q g₁H),ew (q g₂H),hu₁,hu₂,h₁.1,h₂.1,?_,?_,
    h₁.2.1,h₂.2.1,h₁.2.2,h₂.2.2⟩
  · intro he
    exact hne₁₂ (hu₁.symm.trans ((congrArg (fun u : S.toSubmodule =>
      ((u.val.toMul:H):G)) (c.injective he)).trans hu₂))
  · apply Commute.map (f := ew.toMonoidHom)
    apply Commute.map (f := q)
    exact Subtype.ext hcomm.eq

end CFSG.Quasithin.Chapter10
