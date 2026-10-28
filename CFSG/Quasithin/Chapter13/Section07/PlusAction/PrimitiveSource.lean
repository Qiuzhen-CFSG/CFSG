module

public import CFSG.Quasithin.Chapter13.Section07.PlusAction.Primitive
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.Residual

/-!
# Primitive witnesses for the original plus section

Apply primitive selection to the kernel of the actual quotient action,
and embed the selected subgroup back in G. The conjugation-section identity
places this subgroup in C_H(UH/U0), so the proved (!) and (*) calculations
and the A.4.8 comparison apply to it. The witness retains the intrinsic
simple-component or odd-chief alternative and the original quotient map.
This supplies the primitive source branch without assuming faithfulness.

Source: Aschbacher--Smith 13.7.4(1), printed pp.936--937.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion PlusAction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The actual primitive witness, with all opening kernel and signalizer
conclusions on its embedded subgroup in G. -/
theorem source_plus_primitive_of_not_faithful
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W}
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hσ : ¬ Function.Injective σ) :
    let U := Section08.Source.UH H V₃
    let U₀ := U ⊓ centralizer (H.pCoreIn 2 : Set G)
    let C := (σ.comp (QuotientGroup.mk' (pCore 2 H))).ker.map H.subtype
    ∃ J : Subgroup H, let K := J.map H.subtype
      IsPrimitiveLift H J ∧ K ≤ C ∧ (K.subgroupOf H).IsSubnormal ∧
      IsPPerfect 2 K ∧ K ≠ ⊥ ∧ ChapterA.Section04.IsFaithfulSignalizerType K ∧
      K ⊓ centralizer (U₀ : Set G) = K.pCoreIn 2 ∧
      ⁅U, K⁆ = ⁅U₀, K⁆ ∧ ⁅U₀, K⁆ ≠ ⊥ ∧
      ⁅U₀, K⁆ ≤ K.pCoreIn 2 ∧ K.pCoreIn 2 ≤ H.pCoreIn 2 ∧
      K.pCoreIn 2 ≤ centralizer (U₀ : Set G) := by
  dsimp only
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  obtain ⟨J, hn, hp, hne, hle, hm⟩ := exists_primitive_action_kernel H σ hσ
  let K := J.map H.subtype
  have hJ : K.subgroupOf H = J := comap_map_eq_self_of_injective H.subtype_injective J
  have hsub : (K.subgroupOf H).IsSubnormal := hJ.symm ▸ hn
  let e := J.equivMapOfInjective H.subtype H.subtype_injective
  have hperfect : IsPPerfect 2 K := hp.of_surjective e.toMonoidHom e.surjective
  have hnontrivial : K ≠ ⊥ := fun hz =>
    hne ((map_eq_bot_iff_of_injective J H.subtype_injective).mp hz)
  have hKC : K ≤ kernel F := (map_mono hle).trans_eq (section_action_kernel (D := F) s)
  refine ⟨J, hm, map_mono hle, hsub, hperfect, hnontrivial,
    source_plus_kernel_faithful_signalizer d h hU hKC hsub hperfect hnontrivial,
    subnormal_fixedLayer_centralizer h hKC hsub, ?_⟩
  exact subnormal_kernel_structure h hKC hsub hperfect hnontrivial

end CFSG.Quasithin.Chapter13.Section07
