module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration.StarSetup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration.FlagCoordinates

/-!
# The binary inner-action or middle-node alternative

The relative local data give a self-centralizing normal component in H*,
and an intrinsic Sylow subgroup inside its specified minimal parabolic.
Recovering deleted basis coordinates lets the checked outer-action theorem
force every non-inner actor to lie in degree four at omitted dimension two.
The existing faithful conjugation construction, composed with the checked
PSL₄(2)–A₈ comparison, then identifies the whole H* with S₈ and its actual
component image with A₈. The original position is retained.

This proves the exceptional extension branch without assuming an extension,
a node action, or a centralizer premise. In the other branch T* ≤ L*; the
rank-two smaller-overgroup generation remains a separate matrix calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1145, the L₄(2), L₅(2) generation paragraph.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OuterAction
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration
variable {G : Type*} [Group G] [Finite G]

lemma inner_or_middleNodeEight {H M L Y T : Subgroup G} {n : ℕ} [NeZero n]
    (d : BinaryLocalData H M L Y T n) :
    starImage H T ≤ starImage H L ∨
      Nonempty (BinaryGeometry.MiddleNodeEight (starImage H L)
        (componentParabolic H L Y T)) := by
  by_cases hinner : starImage H T ≤ starImage H L
  · exact Or.inl hinner
  right
  let _ : (starImage H L).Normal := star_component_normal d.reduced
  have hc := star_component_centralizer d
  obtain ⟨S, hSP⟩ := component_sylow_le_parabolic d.reduced
  rcases d.dimension with hn | hn
  · subst n
    obtain ⟨b, i, hi, hP⟩ := position_deletedFlag (by decide : 2 ≤ 3) d.position S hSP
    have hmiddle := (normalizing_deletedFlag_alternative (by decide : 2 ≤ 3)
      (by decide : 3 ≤ 4) d.position.model b i
      (componentParabolic H L Y T) (starImage H T) hP hc d.invariant).resolve_left hinner
    have hk : starImage H L ≠ ⊤ := by
      intro he
      exact hinner (he ▸ le_top)
    exact ⟨⟨d.position, hi.symm.trans hmiddle.2,
      markedSymmetricExtension d.position.model hc hk,
      markedSymmetricExtension_component_image d.position.model hc hk⟩⟩
  · subst n
    obtain ⟨b, i, _, hP⟩ := position_deletedFlag (by decide : 2 ≤ 4) d.position S hSP
    have hmiddle := (normalizing_deletedFlag_alternative (by decide : 2 ≤ 4)
      (by decide : 4 ≤ 4) d.position.model b i
      (componentParabolic H L Y T) (starImage H T) hP hc d.invariant).resolve_left hinner
    omega
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration
