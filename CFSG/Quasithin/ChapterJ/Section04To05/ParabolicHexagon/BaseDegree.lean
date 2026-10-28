module

public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.AdjacencyReduction
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.EndpointAction.Fixed
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Labels.BaseEndpoints

/-!
# The two neighbors of the original base parabolic

A commuting-five incidence is conjugated to the original five subgroup by an
actor in the base endpoint normalizing the marked four-group. The proved
endpoint action fixes every member of the six-parabolic family. The fixed-five
centralizer calculation and uniqueness of a parabolic label therefore give
exactly the two original neighbors, without a recognition or Small premise.

Source: Aschbacher–Smith, J.4.10, printed pp.444–445.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
open Tits.ExceptionalParabolics.FullRee
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
variable {D:Type*} [Group D] (q:Completion D)
  {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (s:SourceChoice p) (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
  (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
  (e:first≃*p.F₁ B5) (f:D→*G)
  (hleft:∀a:first,f (q.left a)=(e a:G)) (hz:(e modelZ:G)=c.z)
  (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)

include q s hi f hleft hfive in
/-- The original base vertex has exactly the two original fixed-five endpoints as neighbors. -/
theorem source_base_neighbors_iff :
    ∃Eu Ezu:globalFamily p B5 c.z (sourceU e),
      (Eu:Subgroup G)∈colorFamily p B5 c.z (sourceU e) (sourceU e) ∧
      (Ezu:Subgroup G)∈colorFamily p B5 c.z (sourceU e) (c.z*sourceU e) ∧
      fixedFive B5 (sourceU e)≤Eu ∧ fixedFive B5 (c.z*sourceU e)≤Ezu ∧
      Eu≠Ezu ∧ ∀E:globalFamily p B5 c.z (sourceU e),
      (sourceGraph p B5 c.z (sourceU e)).Adj (baseVertex p B5 c e hz) E ↔ E=Eu∨E=Ezu := by
  obtain ⟨Eu,Ezu,hEu,hEzu,hBu,hBzu,hne,huadj,hzuadj⟩:=
    source_base_neighbor_endpoints p s B5 hi c e hz hfive q f hleft
  refine ⟨Eu,Ezu,hEu,hEzu,hBu,hBzu,hne,?_⟩
  intro E
  constructor
  · intro hadj
    obtain ⟨v,hv,hEv⟩:=E.property
    have hraw := (Subgroup.PrimeIncidence.adj_iff 5 (pairSpan c.z (sourceU e))
      (p.F₁ B5) (E:Subgroup G)).mpr ((sourceGraph_adj_iff p B5 c.z (sourceU e) _ _).mp hadj)
    obtain ⟨n,hn,hc,hnN,hEn,hB⟩:=source_adjacent_fixed_reduction p B5 c e hz q f hleft
      hfive hv hEv hraw
    have hfix:E.val.conjBy n=E.val :=
      EndpointAction.endpointNormalizer_fixes_global q p s c B5 hi e f hleft hz hfive
        n ⟨hn,hnN⟩ E.val E.property
    rw [hfix] at hB
    obtain ⟨hu,hI⟩:=source_inverter c B5 e hz hfive
    have hcards:=source_three_fives c B5 (sourceU e) hu
      (PathTransport.source_fusion q c e f hleft hz) hI
    simp only [colors,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
    rcases hv with rfl|rfl|rfl
    · exact False.elim (sourceGraph_not_adj_base_color p s B5 hi c e hz _ E
        (first_mem_color p B5 c e hz) hEv hadj)
    · exact Or.inl (Subtype.ext (color_members_eq_of_five p s B5 hi c e hEv hEu
        hcards.1 hB hBu))
    · exact Or.inr (Subtype.ext (color_members_eq_of_five p s B5 hi c e hEv hEzu
        hcards.2.1 hB hBzu))
  · rintro (rfl|rfl)
    · exact huadj
    · exact hzuadj
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
