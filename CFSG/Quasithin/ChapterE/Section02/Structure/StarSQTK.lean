module
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.Quasithin.NormalTwoQuotient

/-!
# SQTK of the actual star quotient

The two-residual of H/J is semisimple by the genuine B.6.8 reduction.
Theorem A applies to that literal section. Every odd-prime Sylow subgroup
of H/J lies in its two-residual, so the resulting rank bound holds on H/J.
The K-group property descends through the original quotient map.

Source: final assertion of Aschbacher–Smith E.2.2, printed p.216.
Only the genuine earlier Theorem A remains explicit.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H]

theorem source_star_sqtk {κ : GroupClass.{u}}
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) :
    IsSQTK κ (H ⧸ ChapterB.minimalParabolicCore T hP) := by
  let J := ChapterB.minimalParabolicCore T hP
  let X := H ⧸ J
  let R := pResidual 2 X
  have hsem : ChapterA.Section02.IsSemisimple R :=
    ChapterB.minimalParabolic_nonsolvable_star_layer T hP hs
  have hsec : ChapterA.Section02.IsSectionOf R H :=
    (ChapterA.Section02.IsSectionOf.subgroup R).ambient_surjective
      (QuotientGroup.mk' J) (QuotientGroup.mk'_surjective J)
  have hr := hA.stronglyQuasithin_section hH.stronglyQuasithin hH.isKGroup hsec hsem
  refine ⟨?_,hH.isKGroup.quotient J⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_le_of_normal_two_quotient R (isPGroup_quotient_pResidual 2) p ho).trans
    (hr p hp ho)
end CFSG.Quasithin.ChapterE.Structure
