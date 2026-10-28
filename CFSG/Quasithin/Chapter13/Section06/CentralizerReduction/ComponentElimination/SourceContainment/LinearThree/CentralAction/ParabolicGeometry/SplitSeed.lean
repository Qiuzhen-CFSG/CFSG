module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.SeedGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.FixedSpace
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.Placement

/-!
# Split seed in the original doubled-module coordinates

The marked seed has order four and centralizes K ∩ T_v. The literal
Thompson image places the model radical in the component Sylow. The
earlier normalizer control and the literal Baumann image supply ambient
seed containment through `Placement.seed_le_UK`. Applying the Sylow
fixed-space calculation then identifies the seed with the plane generated
by (x,0) and (0,x), for nonzero x with last coordinate zero.

`exists_split_seed` chooses the original doubled marking. In particular,
its actor and literal action map agree with the supplied marking, so the
parent can use its separately constructed parabolic normalizer image.
The two three-dimensional summands, their invariant binary planes, and
the two-dimensional seed spanned by these points remain distinct.

This completes the split-seed construction under the full standing
Hypothesis 13.3.1, the genuine earlier local conclusions, hypothetical
centrality, and the two explicit Thompson/Baumann radical-image equalities.
The parent parabolic-geometry assembly must discharge those equalities
and apply the terminal obstruction; this is not the full Lemma 13.6.20.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 13.6.20, printed p.931.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed
open ComponentSelection A5Module
variable {G : Type*} [Group G] [Finite G] {K L V : Subgroup G}

/-- The central branch supplies the split points in one chosen compatible
marking, retaining the same actor and action map. The proof first establishes
literal ambient seed placement; `subgroupOf` is not used as a substitute for
that containment. The original module coordinates suffice, with y = x. -/
theorem exists_split_seed
    (T : Sylow 2 G) (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (Uv (markedZ s) (markedV s))]
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ s) (markedV s))
    (hn : Tv (T : Subgroup G) (markedV s) ≤ normalizer (K : Set G))
    (hL : Tv (T : Subgroup G) (markedV s) ≤ normalizer (Lv L (markedV s) : Set G))
    (hz : Tv (T : Subgroup G) (markedV s) ≤ centralizer ({markedZ s} : Set G))
    (d : DoubledCoordinates K L (T : Subgroup G) (markedZ s) (markedV s) hK.1.1 hL hz)
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))).map (Gv (markedV s)).subtype =
      Tv (T : Subgroup G) (markedV s))
    (h1364 : ChapterB.baumann (T : Subgroup G) =
      ChapterB.baumann (Tv (T : Subgroup G) (markedV s)))
    (h1365 : Gv (markedV s) ⊓ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      Mv (normalizer (L : Set G)) (markedV s))
    (hlocal : Mv (normalizer (L : Set G)) (markedV s) =
      normalizer (V : Set G) ⊓ Gv (markedV s))
    (hc : ⁅plusImage K L (T : Subgroup G) (markedZ s) (markedV s) hL hz K,
      plusImage K L (T : Subgroup G) (markedZ s) (markedV s) hL hz (Lv L (markedV s))⁆ = ⊥)
    (hJ : plusImage K L (T : Subgroup G) (markedZ s) (markedV s) hL hz
      (Stellmacher.elementaryAbelianMaxJ (Tv (T : Subgroup G) (markedV s))) =
      BinaryLinearThree.R.map (modelEmbedding d))
    (hB : plusImage K L (T : Subgroup G) (markedZ s) (markedV s) hL hz
      (ChapterB.baumann (T : Subgroup G)) = BinaryLinearThree.R.map (modelEmbedding d)) :
    ∃ d' : DoubledCoordinates K L (T : Subgroup G) (markedZ s) (markedV s) hK.1.1 hL hz,
      d'.actor = d.actor ∧ d'.actionMap = d.actionMap ∧
      ∃ x y : BinaryLinearThree.Vector, x 2 = 0 ∧ x ≠ 0 ∧
        ((⁅zpowers (markedZ s), Lv L (markedV s)⁆ : Subgroup G).subgroupOf
          (UK K L (T : Subgroup G) (markedZ s) (markedV s))).map
            d'.moduleEquiv.toMonoidHom =
              (BinaryLinearThree.DoubledParabolic.splitPlane x y).toAddSubgroup.toSubgroup := by
  have hplace := Placement.seed_le_UK T standing s hK hn hL hz d S hS
    h1364 h1365 hlocal hc hJ hB
  obtain ⟨x, hx, hne, hQ⟩ := split_seed_of_placement s hK.1.1 hL hz d S hS hn hc hJ hplace
  exact ⟨d, rfl, rfl, x, x, hx, hne, hQ⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed
