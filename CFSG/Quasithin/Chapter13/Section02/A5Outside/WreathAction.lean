module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.WholeActor
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.WreathActor

/-!
# The original S₃ or S₃≀C₂ actor, with its entire moved action

The preceding source theorem identifies the faithful outside quotient with
the full natural SL₂(2) or binary orthogonal actor. The actual orthogonal
isometry/wreath equivalence gives the printed wreath model and retains
pointwise compatibility with the original moved vectors. The canonical
centralizer quotient is unchanged.

Source: Aschbacher–Smith 13.2.8(3), printed p.880.
-/
@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- Literal whole S₃/wreath action of H/C_H(〈Ω₁Z(T)^H〉). -/
theorem source_solvable_wreath_omega_action
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    ChapterB.SmallNaturalWreathAction (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) := by
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  exact (source_solvable_whole_omega_action d hH hB hZ hs).wreath

end CFSG.Quasithin.Chapter13.Section02.A5Outside
