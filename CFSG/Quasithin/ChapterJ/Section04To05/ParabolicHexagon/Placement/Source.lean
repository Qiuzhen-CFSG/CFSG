module
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.Placement.Graph
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.Placement.Frame
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.Placement.Stabilizer
/-!
# Placement of the original fixed five in the fourth point stabilizer

The actual source actor j takes the base point to the marked fourth point,
sends z to u and fixes zu. In the source quotient frame, its conjugate has
order two and differs from the original inverter. Literal quotient transport,
the proved six-cycle, and the original stabilizer map then place C_P(u) in
the mapped fourth point stabilizer. Quotient commutation is derived here,
so it is not an additional actor hypothesis.

The point/label actor and its two quotient facts are the preceding source
geometry producer; all pentagon action, graph placement and map transport
premises are discharged in this consumer. Source: Aschbacher--Smith proof
of J.4.7, printed pp.444--445.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ChapterF.SourceCompletion.BinaryRee Subgroup.CosetGeometry.RankTwo
variable {D:Type*} [Group D] (q:Completion D)
  {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (s:SourceChoice p) (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
  (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
  (e:first≃*p.F₁ B5) (f:D→*G)
  (hleft:∀a:first,f (q.left a)=(e a:G)) (hz:(e modelZ:G)=c.z)
  (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
include q s hi f hleft hz hfive

theorem fixedFive_placement_of_actor (j:D) (k:G)
    (hjpoint:j • base q.family false=completionFourthWord q • base q.family false)
    (hjz:f j*c.z*(f j)⁻¹=sourceU e)
    (hjt:f j*(c.z*sourceU e)*(f j)⁻¹=c.z*sourceU e)
    (hk:k∈normalizer (pairSpan c.z (sourceU e):Set G))
    (hkcolor:k*(c.z*sourceU e)*k⁻¹=c.z) (hkz:k*c.z*k⁻¹=sourceU e)
    (a:d.toTypeRuSetup.H) (ha:(a:G)=k*(f j)*k⁻¹)
    (hao:orderOf (d.ru2.quotientMap a)=2)
    (hane:d.ru2.quotientMap a≠d.ru2.quotientMap (sourceInverter p B5 e)) :
    fixedFive B5 (sourceU e)≤
      (stabilizer q.family (completionFourthWord q • base q.family false)).map f := by
  rw [mapped_fourth_of_point_transport q e f hleft j hjpoint]
  apply fixedFive_le_conjugate_of_quotient_actor q p s c B5 hi e f hleft hz hfive
    (f j) k hjz hjt hk hkcolor a ha hao hane
  exact quotient_actor_commutes p c B5 e hz (f j) k hjz hkcolor hkz a ha
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
