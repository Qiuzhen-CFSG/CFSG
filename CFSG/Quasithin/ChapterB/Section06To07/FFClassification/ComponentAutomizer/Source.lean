module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentAutomizer
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.StarFactors
public import FeitThompson.FinalTheorem

/-!
# The original nonsolvable source automizer

Start with the original finite nonsolvable minimal parabolic and its chosen
Sylow. The proved core quotient theorem supplies a transitive simple
component of the literal star residual. The odd-order theorem proves that
this component has even order. The new automizer theorem then gives the
minimal-parabolic property of N(L)/C(L), with exactly the original
normalizer-Sylow image. No automizer or even-order conclusion is an input.

Source: Aschbacher–Smith, B.6.8(3), used in B.6.9 and E.2.3, printed
pp.114–116 and216–217 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- The literal core quotient retains minimal parabolicity at the actual Sylow image. -/
theorem minimalParabolic_star_minimalParabolic
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) :
    IsMinimalParabolicOver (minimalParabolicStarSylow T hP) ⊤ := by
  have he : minimalParabolicStarSylow T hP =
      T.mapSurjective (QuotientGroup.mk'_surjective (minimalParabolicCore T hP)) := by
    apply Sylow.ext
    exact minimalParabolicStarSylow_coe T hP
  rw [he]
  exact minimalParabolic_map_of_kernel_le_core T hP _
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])

/-- B.6.8's actual simple-factor automizer, constructed from the original source hypotheses. -/
theorem minimalParabolic_nonsolvable_star_automizer
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) :
    ∃ L : Subgroup (minimalParabolicStarQuotient T hP),
      L ≤ pResidual 2 (minimalParabolicStarQuotient T hP) ∧
      IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
      IsComponent (minimalParabolicStarQuotient T hP) L ∧
      componentOrbit L (minimalParabolicStarSylow T hP) =
        pResidual 2 (minimalParabolicStarQuotient T hP) ∧
      ∃ S : Sylow 2 (NormalizerAction.Star L),
        (S : Subgroup (NormalizerAction.Star L)) =
          ((minimalParabolicStarSylow T hP : Subgroup _).subgroupOf
            (normalizer (L : Set (minimalParabolicStarQuotient T hP)))).map
              (NormalizerAction.quotient L) ∧
        IsMinimalParabolicOver S ⊤ := by
  obtain ⟨L,hLR,hLs,hLa,hL,ho⟩ := minimalParabolic_nonsolvable_star_factor T hP hs
  let := hLs
  let := hL.2
  have heven : 2 ∣ Nat.card L := by
    by_contra hn
    have hodd : Odd (Nat.card L) := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using hn)
    exact Group.IsPerfect.not_isSolvable L (odd_order_theorem L hodd)
  exact ⟨L,hLR,hLs,hLa,hL,ho,component_automizer_minimalParabolic
    (minimalParabolicStarSylow T hP) (minimalParabolic_star_minimalParabolic T hP)
    hL heven ho⟩

end CFSG.Quasithin.ChapterB
