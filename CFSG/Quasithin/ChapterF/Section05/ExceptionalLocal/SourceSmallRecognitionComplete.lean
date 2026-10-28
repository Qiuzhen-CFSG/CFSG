module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerEndpointPair
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.SourceSmallRecognition
/-!
# The original F.5.5 completion recognition

The source hypotheses supply the required fixed-endpoint involutions and
their order-four product. The F.4.26 quadrangle recognition therefore gives
a comparison preserving both literal endpoint ranges, with no extra local
recognition or placement premise.

Source: Aschbacher--Smith F.5.5(4), printed p.302.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)

include h in
theorem source_parabolic_preserving_equiv :
    ∃ e : G0≃*Extension.ProjectiveExtension 1 hn,
      c.left.range.map e.toMonoidHom=Extension.point 1 hn ∧
      c.right.range.map e.toMonoidHom=Extension.plane 1 hn := by
  obtain ⟨s,t,hs,ht,hsout,htout,hs2,ht2,hst⟩:=source_fixed_endpoint_pair c i z h
  exact source_parabolic_preserving_equiv_of_fixed_endpoints c i h.embedding_injective
    s t hs ht hsout htout hs2 ht2 hst

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
