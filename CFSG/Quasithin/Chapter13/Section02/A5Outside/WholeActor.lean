module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.Setup
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalNormality
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.WholeActor

/-!
# The full solvable outside action in the original A₅ source

For an original outside H moving Ω₁Z(T), the already proved E.2.3 setup
applies to U=〈Ω₁Z(T)^H〉. The full faithful quotient H/C_H(U) acts naturally
on its original offender moved space as SL₂(2) or O₄⁺(2). This is the full
actor part of 13.2.8(3), keeping the exact quotient map. The two earlier
Chapter5 inputs are the Baumann normalizer bound and solvability of H;
13.2.9's stronger C_H(U)=O₂(H) assertion is a separate source step.

Source: Aschbacher–Smith 13.2.8(3), printed p.880.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- Full natural quotient action on the original outside Ω-center orbit module. -/
theorem source_solvable_whole_omega_action
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
    ChapterB.SmallNaturalMovedAction (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) := by
  obtain ⟨hsq,_,hp,hU,hj⟩ := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  let := hs
  exact ChapterE.ThompsonAction.source_solvable_whole_actor _ hp _ hU hj
    (hsq.stronglyQuasithin 3 (by decide) (by decide)) inferInstance

end CFSG.Quasithin.Chapter13.Section02.A5Outside
