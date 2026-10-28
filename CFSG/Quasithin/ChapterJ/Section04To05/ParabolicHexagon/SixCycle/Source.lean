module
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.SixCycle.Coordinates
public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.SixCycle
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
open ChapterF.SourceCompletion.BinaryRee
variable {D:Type*} [Group D] (q:Completion D)
  {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (s:SourceChoice p) (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
  (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
  (e:first≃*p.F₁ B5) (f:D→*G)
  (hleft:∀a:first,f (q.left a)=(e a:G)) (hz:(e modelZ:G)=c.z)
  (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
include q s hi f hleft hz hfive

theorem source_vertex_in_base_orbit (E:globalFamily p B5 c.z (sourceU e)) :
    ∃n:G,n∈normalizer (pairSpan c.z (sourceU e):Set G) ∧ (p.F₁ B5).conjBy n=(E:Subgroup G) := by
  obtain ⟨v,hiV,_,_,_,horb,_⟩ := source_cycle_coordinates q p s c B5 hi e f hleft hz hfive
  have hs:Function.Surjective v := (hiV.bijective_of_nat_card_le (by
    rw [Nat.card_fin,source_global_family_card q p s c B5 hi e f hleft hz hfive])).2
  obtain ⟨i,rfl⟩:=hs E
  exact horb i

theorem source_neighbor_card (E:globalFamily p B5 c.z (sourceU e)) :
    Nat.card ((sourceGraph p B5 c.z (sourceU e)).neighborSet E)=2 := by
  obtain ⟨Eu,Ezu,_,_,_,_,hne,hbase⟩:=source_base_neighbors_iff q p s c B5 hi e f hleft hz hfive
  have hc:Nat.card ((sourceGraph p B5 c.z (sourceU e)).neighborSet (baseVertex p B5 c e hz))=2 := by
    have he:(sourceGraph p B5 c.z (sourceU e)).neighborSet (baseVertex p B5 c e hz)={Eu,Ezu}:=
      Set.ext fun F=>hbase F
    rw [he,Nat.card_coe_set_eq,Set.ncard_pair hne]
  obtain ⟨n,hn,hE⟩:=source_vertex_in_base_orbit q p s c B5 hi e f hleft hz hfive E
  let a:=sourceGraphEquiv p B5 c e hz n hn
  have ha:a (baseVertex p B5 c e hz)=E := by
    apply Subtype.ext
    rw [sourceGraphEquiv_apply,baseVertex_coe]
    exact hE
  have hh:=Nat.card_congr (a.mapNeighborSet (baseVertex p B5 c e hz))
  rw [ha] at hh
  exact hh.symm.trans hc

theorem source_cycle_iso :
    ∃ι:SimpleGraph.cycleGraph 6 ≃g sourceGraph p B5 c.z (sourceU e),
      ι 0=baseVertex p B5 c e hz ∧
      (∀i,(ι i:Subgroup G)∈colorFamily p B5 c.z (sourceU e) (colorWord c.z (sourceU e) i)) ∧
      fixedFive B5 (sourceU e)≤ι 1 ∧ fixedFive B5 (c.z*sourceU e)≤ι 5 ∧
      nextFive c B5 (sourceU e)≤ι 2 := by
  obtain ⟨v,hinj,hv0,hcolors,hedges,_,hBu,hBzu,hnext⟩ :=
    source_cycle_coordinates q p s c B5 hi e f hleft hz hfive
  obtain ⟨ι,hι⟩ := SimpleGraph.SixCycle.equiv_of_edges
    (sourceGraph p B5 c.z (sourceU e))
    (source_global_family_card q p s c B5 hi e f hleft hz hfive) v hinj
    (source_neighbor_card q p s c B5 hi e f hleft hz hfive) hedges
  refine ⟨ι,?_,?_,?_,?_,?_⟩
  · rw [hι,hv0]
  · intro i;rw [hι];exact hcolors i
  · rw [hι];exact hBu
  · rw [hι];exact hBzu
  · rw [hι];exact hnext
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.SixCycle
