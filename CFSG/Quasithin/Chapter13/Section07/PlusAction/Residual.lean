module

public import CFSG.Quasithin.Chapter13.Section07.PlusAction.LocalExclusion

/-!
# A genuine residual witness when the original plus action is not faithful

The two-residual of C=C_H(UH/U0) is normal in H. If C exceeds QH,
that residual is nontrivial: otherwise C would be a normal two-group
and hence lie in QH. The previous source calculations place this actual
residual in X_f, outside M, and identify its kernel on U0 with its own
two-core. This gives a concrete witness for the contradiction argument,
without postulating a nontrivial component or a trivial action kernel.

The subsequent selection of a component or minimal odd normal image,
and the model exclusions on pp.937--938, remain to be established.
Source: Aschbacher--Smith13.7.4(1), printed pp.936--938.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]

def kernelResidual (D : ChapterF.Section09.Setup G) : Subgroup G :=
  (pResidual 2 (kernel D)).map (kernel D).subtype

variable {D : ChapterF.Section09.Setup G}

omit [Finite G] in
theorem kernelResidual_le : kernelResidual D ≤ kernel D := map_subtype_le _

omit [Finite G] in
theorem kernelResidual_normalized : D.H ≤ normalizer (kernelResidual D : Set G) :=
  kernel_normalized.trans (normalizer_le_normalizer_characteristic_image
    (kernel D) (pResidual 2 (kernel D)))

theorem kernelResidual_perfect : IsPPerfect 2 (kernelResidual D) :=
  isPPerfect_embedded_pResidual 2 (kernel D)

theorem kernelResidual_ne_bot (h : D.Hypothesis) (hne : kernel D ≠ D.QH) :
    kernelResidual D ≠ ⊥ := by
  intro hz
  have hr : pResidual 2 (kernel D) = ⊥ := by
    apply map_injective (kernel D).subtype_injective
    simpa only [kernelResidual, Subgroup.map_bot] using hz
  have hp : IsPGroup 2 (kernel D) := by
    apply (isPGroup_quotient_pResidual 2 (G := kernel D)).of_injective
      (QuotientGroup.mk' (pResidual 2 (kernel D)))
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk', hr]
  exact hne (le_antisymm (le_pCoreIn_of_normalizes hp kernel_le_H kernel_normalized)
    (core_le_kernel h))

omit [Finite G] in
/-- Nonfaithfulness of the actual quotient representation forces its
literal lifted kernel to exceed the original two-core. -/
theorem quotient_action_kernel_ne_core {H : Subgroup G}
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (hne : ¬ Function.Injective σ) :
    (σ.comp (QuotientGroup.mk' (pCore 2 H))).ker.map H.subtype ≠ H.pCoreIn 2 := by
  intro he
  apply hne
  apply (MonoidHom.ker_eq_bot_iff σ).mp
  apply eq_bot_iff.mpr
  intro a ha
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) a
  have hx : (x : G) ∈ (σ.comp (QuotientGroup.mk' (pCore 2 H))).ker.map H.subtype :=
    mem_map_of_mem H.subtype ha
  rw [he] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  exact (QuotientGroup.eq_one_iff (N := pCore 2 H) x).mpr
    ((Subtype.ext hyx : y = x) ▸ hy)

end CFSG.Quasithin.Chapter13.Section07.PlusAction

namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion PlusAction
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- A concrete original-group witness for the contrary-faithfulness branch.
The structural source inputs only discharge the earlier K outside M step. -/
theorem source_plus_residual_of_not_faithful
    (h1223 : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Chapter12.Section02.Structural1222.{u} KnownSimple.IsKnownSimple)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W}
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hσ : ¬ Function.Injective σ) :
    let U := Section08.Source.UH H V₃
    let U₀ := U ⊓ centralizer (H.pCoreIn 2 : Set G)
    let C := (σ.comp (QuotientGroup.mk' (pCore 2 H))).ker.map H.subtype
    ∃ K : Subgroup G, K ≤ C ∧ H ≤ normalizer (K : Set G) ∧
      ChapterA.Section04.IsFaithfulSignalizerType K ∧ ¬ K ≤ M ∧
      K ⊓ centralizer (U₀ : Set G) = K.pCoreIn 2 ∧
      ⁅U, K⁆ = ⁅U₀, K⁆ ∧ ⁅U₀, K⁆ ≠ ⊥ ∧
      ⁅U₀, K⁆ ≤ K.pCoreIn 2 ∧ K.pCoreIn 2 ≤ H.pCoreIn 2 ∧
      K.pCoreIn 2 ≤ centralizer (U₀ : Set G) := by
  dsimp only
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := kernelResidual F
  have he := section_action_kernel (D := F) s
  change (σ.comp (QuotientGroup.mk' (pCore 2 H))).ker.map H.subtype = kernel F at he
  have hCne : kernel F ≠ F.QH := he ▸ quotient_action_kernel_ne_core σ hσ
  have hKne : K ≠ ⊥ := kernelResidual_ne_bot h hCne
  have hn : (K.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (kernelResidual_normalized (D := F))
  have hfaith := source_plus_kernel_faithful_signalizer d h hU
    (kernelResidual_le (D := F)) hn.isSubnormal (kernelResidual_perfect (D := F)) hKne
  have hout := normal_kernel_not_le_local d h1223 structural h hU hV hne
    (kernelResidual_le (D := F)) (kernelResidual_normalized (D := F))
      (kernelResidual_perfect (D := F)) hKne
  refine ⟨K, he.symm ▸ (kernelResidual_le (D := F)), (kernelResidual_normalized (D := F)), hfaith, hout,
    subnormal_fixedLayer_centralizer h (kernelResidual_le (D := F)) hn.isSubnormal, ?_⟩
  exact subnormal_kernel_structure h (kernelResidual_le (D := F)) hn.isSubnormal
    (kernelResidual_perfect (D := F)) hKne

end CFSG.Quasithin.Chapter13.Section07
