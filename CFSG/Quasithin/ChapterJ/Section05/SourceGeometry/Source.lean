module
public import CFSG.Quasithin.ChapterJ.Section05.SourceGeometry.Parameters
/-!
# Original-source J.5.4(3) and J.5.5(1–3)

The original J.4 subgroup, marked recognition, and unchanged local choices
construct a faithful primitive rank-three graph on G/F. Its local building
coordinates prove the exact source parameters and adjacent sphere classes.
The remaining recognition input is the genuine earlier marked J.4.7 theorem.
-/

public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices Tits.ExceptionalParabolics.FullRee
variable {G:Type*} [Group G] [Finite G]

theorem SourceChoice.source_J_5_4_5 {d:LocalSetup G} (p:Plane d) (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic) (e:p.F B5 X≃*ReeF4.Model 0)
    (hmark:((p.F₁ B5).subgroupOf (p.F B5 X)).map e.toMonoidHom=first)
    (P:Sylow 5 (p.F B5 X)) :
    ∃(q g:G) (hq:q∉p.F B5 X) (hs:q•(q•basePoint (p.F B5 X))=basePoint (p.F B5 X))
      (h:RudvalisAction (p.F B5 X) (q•basePoint (p.F B5 X)) (g•basePoint (p.F B5 X))),
      q∈d.toTypeRuSetup.Q ∧
      g∈normalizer (((P:Subgroup (p.F B5 X)).map (p.F B5 X).subtype):Set G) ∧
      g∉p.F B5 X ∧
      Nat.card ((sourceGraph (p.F B5 X) q hq hs).commonNeighbors
        (basePoint (p.F B5 X)) (q•basePoint (p.F B5 X)))=730 ∧
      Nat.card ((sourceGraph (p.F B5 X) q hq hs).commonNeighbors
        (basePoint (p.F B5 X)) (g•basePoint (p.F B5 X)))=780 ∧
      (∀v:orbit (p.F B5 X) (q•basePoint (p.F B5 X)),
        (sourceGraph (p.F B5 X) q hq hs).Adj (q•basePoint (p.F B5 X)) v.val ↔
          h.localDistance ⟨q•basePoint (p.F B5 X),mem_orbit_self _⟩ v=1 ∨
          h.localDistance ⟨q•basePoint (p.F B5 X),mem_orbit_self _⟩ v=2 ∨
          h.localDistance ⟨q•basePoint (p.F B5 X),mem_orbit_self _⟩ v=3) := by
  obtain ⟨q,g,hq,hqF,hg,hgF,hs,⟨h⟩⟩:=SourceChoice.source_rank_three p s B5 hi X e hmark P
  have hp:=h.parameters (p.F B5 X) q hqF hs
  have ho:=h.source_J_5_5_three_suborbits (p.F B5 X) q hqF hs
  exact ⟨q,g,hqF,hs,h,hq,hg,hgF,hp.1,hp.2,ho.1⟩

attribute [local instance] Classical.propDecidable

/-- The literal source graph is strongly regular with the J.5.5 parameters. -/
theorem RudvalisAction.source_srg (F:Subgroup G) (q:G) (hq:q∉F)
    (hs:q•(q•basePoint F)=basePoint F) {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F)) [Fintype (Cosets F)] :
    (sourceGraph F q hq hs).IsSRGWith 4060 1755 730 780 := by
  have hh:=h.stronglyRegular F q hq hs
  obtain ⟨hlam,hmu⟩:=h.parameters F q hq hs
  rwa [hlam,hmu] at hh

end CFSG.Quasithin.ChapterJ.Section05
