module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration.Lifting
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration.Outer
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration.RankTwoFour
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration.RankTwoFive

/-!
# Binary parabolic generation and the middle-node alternative

The outer branch is complete: `inner_or_middleNodeEight` proves that either
T* lies in L*, or H* is compatibly S₈ with L* its A₈ and omitted node two.
All normality, centralizer, flag-coordinate and extension premises are derived
from `BinaryLocalData`.

In the inner branch H* = L*. The original parabolic is exactly Y*T*, since
the Sylow contains the quotient kernel. Thus its intrinsic small component
overgroups are genuine star overgroups of Y*T*. Lifting a nonempty generating
family gives actual overgroups K of YT in H with the required literal
K/O₂(K) equivalences. The degree-four and degree-five rank-two constructions
provide this family for every omitted node. Their contained Sylow premise
follows by intersecting the source Sylow with the normal component and
taking its star image.

`generation_or_middleNodeEight` establishes the source alternative directly
from `BinaryLocalData`, discharging both generation premises of the preserved
conditional helper `alternative_of_component_generation`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1144–1145, especially the binary generation paragraph on p.1145.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration
variable {G : Type*} [Group G] [Finite G]

lemma generation_of_inner_component {H M L Y T : Subgroup G}
    (d : ReducedLocalData H M L Y T) (hinner : starImage H T ≤ starImage H L)
    (hne : (smallComponentOvergroups (starImage H L) (componentParabolic H L Y T)).Nonempty)
    (hgen : starImage H L ≤
      sSup (smallComponentOvergroups (starImage H L) (componentParabolic H L Y T))) :
    H ≤ sSup (smallOvergroups H Y T) := by
  have htop : starImage H L = ⊤ := by
    have he := star_generation d
    rwa [sup_eq_left.mpr hinner] at he
  have hsub : smallComponentOvergroups (starImage H L) (componentParabolic H L Y T) ⊆
      smallStarOvergroups H Y T := by
    intro P hP
    refine ⟨?_, hP.2.2⟩
    rw [← parabolic_eq_base_of_inner d hinner]
    exact hP.1
  apply generation_of_star_generation (d.cubic_in_component.trans (component_le d)) (sylow_le d)
  · exact hne.mono hsub
  · exact htop.symm.le.trans (hgen.trans (sSup_le_sSup hsub))

/-- Conditional assembly of the source alternative from the intrinsic rank-two
matrix-generation result. The latter remains an explicit premise. -/
lemma alternative_of_component_generation {H M L Y T : Subgroup G} {n : ℕ} [NeZero n]
    (d : BinaryLocalData H M L Y T n)
    (hne : (smallComponentOvergroups (starImage H L) (componentParabolic H L Y T)).Nonempty)
    (hgen : starImage H L ≤
      sSup (smallComponentOvergroups (starImage H L) (componentParabolic H L Y T))) :
    H ≤ sSup (smallOvergroups H Y T) ∨
      Nonempty (BinaryGeometry.MiddleNodeEight (starImage H L)
        (componentParabolic H L Y T)) := by
  rcases inner_or_middleNodeEight d with hinner | houter
  · exact Or.inl (generation_of_inner_component d.reduced hinner hne hgen)
  · exact Or.inr houter

/-- The binary generation alternative on printed p.1145: either the actual
overgroups of YT with intrinsic quotient S₃ × S₃ or PSL₃(2) generate H, or
H/O₂(H) is compatibly S₈ with component A₈ and omitted flag dimension two.
All Sylow, generation and extension premises are derived from the local data. -/
theorem generation_or_middleNodeEight {H M L Y T : Subgroup G} {n : ℕ} [NeZero n]
    (d : BinaryLocalData H M L Y T n) :
    H ≤ sSup (smallOvergroups H Y T) ∨
      Nonempty (BinaryGeometry.MiddleNodeEight (starImage H L)
        (componentParabolic H L Y T)) := by
  obtain ⟨S, hSP⟩ := component_sylow_le_parabolic d.reduced
  have hgen :
      (smallComponentOvergroups (starImage H L) (componentParabolic H L Y T)).Nonempty ∧
      starImage H L ≤
        sSup (smallComponentOvergroups (starImage H L) (componentParabolic H L Y T)) := by
    rcases d.dimension with hn | hn
    · subst n
      exact rankTwoFour_generation d.position S hSP
    · subst n
      exact rankTwoFive_generation d.position S hSP
  exact alternative_of_component_generation d hgen.1 hgen.2

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration
