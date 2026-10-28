module
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.Placement.Source
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SixPath.Quotient
/-!
# The source fixed five at the actual fourth point

The frame is constructed by the two original involution reflections. The
six-path actor and the order-three centralizer transporter give distinct
commuting involutions in the literal H/Q quotient. Pentagon swapping and
the six-parabolic cycle then place the original fixed five in the mapped
fourth-point stabilizer. This discharges the placement premise of the
source J.4-to-J.5 recognition consumer without assuming smallness or a
whole-completion identification. Source: J.4.7, printed p.444.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
open Centralizers Centralizers.Choices MarkedInverter PathTransport
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ChapterF.SourceCompletion.BinaryRee Subgroup.CosetGeometry.RankTwo
variable {D:Type*} [Group D] (q:Completion D)
  {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (s:SourceChoice p) (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
  (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
  (e:first≃*p.F₁ B5) (f:D→*G) (hf:Function.Injective f)
  (hleft:∀a:first,f (q.left a)=(e a:G)) (hz:(e modelZ:G)=c.z)
  (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)

include s c hi hf hleft hz hfive in
theorem source_fixedFive_placement :
    fixedFive B5 (sourceU e)≤
      (stabilizer q.family (completionFourthWord q • basePoint q)).map f := by
  obtain ⟨k,hk,hkc,hkz⟩:=exists_quotient_frame q p c B5 e f hleft hz hfive
  obtain ⟨j,hjpoint,hjz,hjt,a,ha,hao,hane⟩:=
    source_quotient_actor q p c B5 e f hf hleft hz hfive k hkc hkz
  exact fixedFive_placement_of_actor q p s c B5 hi e f hleft hz hfive
    j k hjpoint hjz hjt hk hkc hkz a ha hao hane
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
