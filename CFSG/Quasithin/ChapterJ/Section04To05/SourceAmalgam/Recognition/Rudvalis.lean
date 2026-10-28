module
public import CFSG.Quasithin.ChapterJ.Section04To05.SourceAmalgam.Recognition.FullRee
public import CFSG.Quasithin.ChapterJ.Section05.SourceRecognition.Rudvalis

/-!
# Original J.4–J.5 recognition: Rudvalis

The preceding source smallness and marked full-Ree recognition construct
the actual rank-three action on G/F. The completed original J.5 uniqueness
argument identifies G with the concrete Rudvalis carrier. All maps and
choices remain those of the original J.4 completion; only its genuine
fixed-five placement remains for the earlier geometric assembly.

Source: Aschbacher–Smith J.4.7–10 and J.5.1–14, printed pp.442–449.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices FiveHexagon.MarkedInverter FiveHexagon.PathTransport
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ChapterF.SourceCompletion.BinaryRee
open Subgroup.CosetGeometry.RankTwo
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

 theorem SourceChoice.rudvalis_of_fixedFive_placement (s:SourceChoice p) (c:Centralizers.Choices d)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic)
    (hm:Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3)))
    (q:Completion (p.F B5 X)) (e:first≃*p.F₁ B5) (e₂:second≃*p.F₂ B5 X)
    (hl:∀a:first,(q.left a:G)=(e a:G)) (hr:∀a:second,(q.right a:G)=(e₂ a:G))
    (hz:(e modelZ:G)=c.z)
    (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
    (hplace:FiveHexagon.fixedFive B5 (sourceU e)≤
      (stabilizer q.family (completionFourthWord q•basePoint q)).map (p.F B5 X).subtype) :
    Nonempty (G≃*Rudvalis.Model) := by
  obtain ⟨E,hE,_,_,_,_⟩:=s.fullRee_of_fixedFive_placement c B5 hi X hm q e e₂ hl hr hz hfive hplace
  let P:Sylow 5 (p.F B5 X):=Classical.choice inferInstance
  obtain ⟨r,g,_,hrF,_,_,hs,⟨h⟩⟩:=Section05.SourceChoice.source_rank_three p s B5 hi X E hE P
  exact h.nonempty_equiv_rudvalis hrF hs
end CFSG.Quasithin.ChapterJ.RuSubgroup
