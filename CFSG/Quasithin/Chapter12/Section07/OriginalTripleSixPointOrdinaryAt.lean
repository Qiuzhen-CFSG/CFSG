module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointSourceAlternative
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointConstrainedExclusion

/-!
# The actual ordinary component at an escaping triple-six point

The original source alternative and complete constrained exclusion make
the literal centralizer-closure of the original residual an ordinary
component. The original point belongs to its center, and its entire center
is its two-core. The subsequent ordinary model inspection identifies the
central quotient and full four-group kernel separately.

Source: Aschbacher--Smith 12.7.5, printed p.840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original escaping point supplies its ordinary literal closure,
without an assumed containing component or any model premise. -/
theorem original_tripleSix_point_ordinary_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬ centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    IsComponent H (B.subgroupOf H) ∧ (t : G) ∈ centerIn B ∧
      centerIn B = B.pCoreIn 2 := by
  rcases original_tripleSix_point_source_alternative_at h structural D a t ht heven hout with
    hordinary | ⟨J,hJ,hq,houtJ,hf,_⟩
  · exact hordinary
  · exact (original_tripleSix_point_no_constrained_at h structural D a t ht heven
      J hJ hq houtJ hf).elim

end CFSG.Quasithin.Chapter12.Section07
