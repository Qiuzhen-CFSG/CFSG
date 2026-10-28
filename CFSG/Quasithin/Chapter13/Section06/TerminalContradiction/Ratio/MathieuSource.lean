module
public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.CocodePreliminary
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.NoFF
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.StrictCode
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuTwentyThree

/-!
# Strict quadratic bounds on the original Mathieu source action

Every quadratic elementary subgroup of M₂₄ has order at most four by the
checked Sylow calculation. The cocode fixed-space centralizer forces every
actor of ratio at most two to have rank greater than two. These incompatible
bounds prove the strict cocode inequality; the literal point embedding gives M₂₃.
The independent checked code calculation and complete whole-action recognition
then give the strict bound on every original center-free M₂₃ source action.

Source: Aschbacher–Smith H.15–16 and K.4.1–3, pp.399–403,458–459.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.MathieuSource
open MathieuCode Sporadic.Mathieu

theorem cocode_two_lt_quadraticRatio : 2 < quadraticRatio cocodeRepresentation := by
  by_contra! hq
  obtain ⟨A,hA,hquad,hs⟩ := (quadraticRatio_le_two_iff _).mp hq
  let := hA.2
  have hc := QuadraticActors.m24_cocode_card_le_four A hquad
  have hr : rank A ≤ 2 :=
    (Nat.log_mono_right hc : Nat.log 2 (Nat.card A) ≤ Nat.log 2 4)
  have hlo := ChapterK.Mathieu.m24_cocode_small_actor_rank A hA hs
  omega

theorem m23Cocode_two_lt_quadraticRatio : 2 < quadraticRatio m23CocodeRepresentation :=
  lt_of_lt_of_le cocode_two_lt_quadraticRatio
    (quadraticRatio_le_of_injective_equivariant m23CocodeRepresentation cocodeRepresentation
      pointEmbedding pointEmbedding_injective (LinearEquiv.refl _ _) (fun _ _ => rfl))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.MathieuSource

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.MathieuSource
open MathieuCode Sporadic.Mathieu
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}
open Theory.GroupTheory

/-- Complete whole-action M₂₃ recognition transports both native strict bounds
to the actual source representation, including its original actor. -/
theorem quadraticRatio_gt_two
    (h : ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting G))
    (hz : center (generalizedFitting G) = ⊥)
    (e : generalizedFitting G ≃* M23) : 2 < quadraticRatio ρ := by
  let eQ := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e
  have hs : ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.SourceHypotheses ρ :=
    ⟨h.sqtk,h.quasisimple,h.faithful,h.irreducible,h.smallCubic⟩
  obtain ⟨_,_,hc | hc⟩ :=
    ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.source_m23_of_degree_and_small_recognition
      ChapterK.SporadicCatalogue.SourceFF.m23_degree_eleven
      ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.m23SmallRecognition ρ hs eQ
  · obtain ⟨f,E,hE⟩ := hc
    exact QuadraticActors.StrictCode.m23Code_quadraticRatio_gt_two.trans_le (quadraticRatio_le_of_injective_equivariant ρ m23CodeRepresentation
      f.toMonoidHom f.injective E hE)
  · obtain ⟨f,E,hE⟩ := hc
    exact m23Cocode_two_lt_quadraticRatio.trans_le
      (quadraticRatio_le_of_injective_equivariant ρ m23CocodeRepresentation
        f.toMonoidHom f.injective E hE)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.MathieuSource
