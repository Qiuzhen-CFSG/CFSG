module
public import CFSG.Quasithin.Chapter13.Section07.ComponentWholeSource
public import Theory.Representation.BinaryOffender.Homogeneous.Core
/-!
# The original Sylow image is faithful on the selected component

The completed13.7.15 conclusions make the entire faithful plus module
an Irr⁺ module for the selected component. A.1.41 makes its linear
centralizer odd, so a two-subgroup centralizing the component fixes the
whole module. Faithfulness kills the actual centralizer in T*.

Source: Aschbacher–Smith13.7.16(1), printed p.944, using A.1.41, p.31.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- Original13.7.16(1): the actual Sylow image acts faithfully on the
selected component. Whole-module Irr⁺ and A.1.41 kill its centralizer. -/
theorem source_plus_sylow_centralizer_eq_bot
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (K : Subgroup H) (hKC : K.IsCComponent) (hK : IsComponent (H ⧸ pCore 2 H)
      (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H))) :
    (((T : Subgroup G).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ⊓
      centralizer (K.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := K.map π
  let S := ((T : Subgroup G).subgroupOf H).map π
  let C := S ⊓ centralizer (J : Set (H ⧸ pCore 2 H))
  have hi := (source_plus_component_irrPlus_and_actor d h hU hV hne g hs hout
    σ s B hB hBA K hK hk hcomm).1
  have hg := source_plus_component_whole d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  rw [hg] at hi
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype.map π
  have hfix := IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes σ hi
    (hS.to_le (show C≤S from inf_le_left))
    (show C≤centralizer (J : Set (H ⧸ pCore 2 H)) from inf_le_right)
    (le_subspaceStabilizer σ ⊤ (by intros; trivial))
  have hf := source_plus_faithful_of_kernel_eq σ s hk
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  apply hf
  ext v
  simpa only [map_one, Module.End.one_apply, MonoidHom.comp_apply, Subgroup.subtype_apply]
    using hfix Submodule.mem_top ⟨x,hx⟩
end CFSG.Quasithin.Chapter13.Section07
