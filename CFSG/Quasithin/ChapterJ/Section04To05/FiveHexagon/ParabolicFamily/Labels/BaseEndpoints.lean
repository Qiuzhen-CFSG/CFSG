module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Labels.Existence
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.Graph

/-!
# The two original neighbors of the base parabolic

The actual fixed five-subgroups C_P(u) and C_P(zu) are centralized by
their labels and normalized by the marked four-group. The source label
theorem places each in its unique colored parabolic. Both commute with
the original B5, so these literal parabolics are distinct neighbors of
the original first endpoint in the source incidence graph.
Source: the adjacency argument of J.4.10, printed p.444.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
open Tits.ExceptionalParabolics.FullRee
open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (p : Plane d) (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
  (hi : ∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹)
  (c : Choices d) (e : first ≃* p.F₁ B5) (hz : (e modelZ : G)=c.z)
  (hfive : (zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
  {D : Type*} [Group D] (q : Completion D) (f : D →* G)
  (hleft : ∀ a : first,f (q.left a)=(e a : G))

include hz

/-- The original endpoint is a member of its z-colored family. -/
theorem first_mem_color : p.F₁ B5 ∈ colorFamily p B5 c.z (sourceU e) c.z := by
  rw [colorFamily_z p B5 c e hz]
  exact ⟨⟨1,conjBy_one _⟩,(e modelU).property⟩

/-- The source graph's base vertex is the literal original first endpoint. -/
def baseVertex : globalFamily p B5 c.z (sourceU e) :=
  ⟨p.F₁ B5,c.z,by simp [colors],first_mem_color p B5 c e hz⟩

theorem baseVertex_coe : (baseVertex p B5 c e hz : Subgroup G)=p.F₁ B5 := rfl

/-- The original marked four-group lies in precisely the transported I. -/
theorem pairSpan_le_sourceI : pairSpan c.z (sourceU e)≤sourceI e := by
  obtain ⟨hzI,huI⟩ := source_marks_mem c e hz
  exact sup_le (zpowers_le.mpr hzI) (zpowers_le.mpr huI)

include s hi hz hfive q f hleft

/-- The original fixed fives each determine exactly one member of their own color. -/
theorem source_fixed_five_labels :
    (∃! E : Subgroup G, E ∈ colorFamily p B5 c.z (sourceU e) (sourceU e) ∧
      fixedFive B5 (sourceU e)≤E) ∧
    (∃! E : Subgroup G, E ∈ colorFamily p B5 c.z (sourceU e) (c.z*sourceU e) ∧
      fixedFive B5 (c.z*sourceU e)≤E) := by
  obtain ⟨hu,hI⟩ := source_inverter c B5 e hz hfive
  have hcards := source_three_fives c B5 (sourceU e) hu
    (PathTransport.source_fusion q c e f hleft hz) hI
  have hVI := pairSpan_le_sourceI p B5 c e hz
  have hm := source_marks_mem c e hz
  exact ⟨source_unique_five_label p s B5 hi c e hz hfive q f hleft
      (sourceU e) (by simp [colors]) (fixedFive B5 (sourceU e)) hcards.1 inf_le_right
      (hVI.trans (sourceI_normalizes_fixed B5 e hfive _ hm.2)),
    source_unique_five_label p s B5 hi c e hz hfive q f hleft
      (c.z*sourceU e) (by simp [colors]) (fixedFive B5 (c.z*sourceU e)) hcards.2.1 inf_le_right
      (hVI.trans (sourceI_normalizes_fixed B5 e hfive _ ((sourceI e).mul_mem hm.1 hm.2)))⟩

/-- Actual original endpoints containing the two fixed fives, with their unique color labels. -/
theorem source_base_neighbor_endpoints :
    ∃ Eu Ezu : globalFamily p B5 c.z (sourceU e),
      (Eu : Subgroup G) ∈ colorFamily p B5 c.z (sourceU e) (sourceU e) ∧
      (Ezu : Subgroup G) ∈ colorFamily p B5 c.z (sourceU e) (c.z*sourceU e) ∧
      fixedFive B5 (sourceU e)≤Eu ∧ fixedFive B5 (c.z*sourceU e)≤Ezu ∧
      Eu≠Ezu ∧
      (sourceGraph p B5 c.z (sourceU e)).Adj (baseVertex p B5 c e hz) Eu ∧
      (sourceGraph p B5 c.z (sourceU e)).Adj (baseVertex p B5 c e hz) Ezu := by
  obtain ⟨hEu,hEzu⟩ := source_fixed_five_labels p s B5 hi c e hz hfive q f hleft
  obtain ⟨Eu,⟨hEu,hBu⟩,_⟩ := hEu
  obtain ⟨Ezu,⟨hEzu,hBzu⟩,_⟩ := hEzu
  obtain ⟨hzo,huo,hne,_⟩ := source_pair_marks p B5 c e hz
  have hz1 : c.z≠1 := by intro hh; rw [hh,orderOf_one] at hzo; omega
  have hu1 : sourceU e≠1 := by intro hh; rw [hh,orderOf_one] at huo; omega
  have hzzu : c.z≠c.z*sourceU e := by
    intro hh
    exact hu1 (mul_left_cancel (show c.z*sourceU e=c.z*1 by simpa only [mul_one] using hh.symm))
  have huzu : sourceU e≠c.z*sourceU e := by
    intro hh
    exact hz1 (mul_right_cancel (show c.z*sourceU e=1*sourceU e by simpa only [one_mul] using hh.symm))
  have hbase := first_mem_color p B5 c e hz
  have hd (v w : G) (hn : v≠w) (E F : Subgroup G)
      (hE : E ∈ colorFamily p B5 c.z (sourceU e) v)
      (hF : F ∈ colorFamily p B5 c.z (sourceU e) w) : E≠F := by
    intro hh
    exact Set.disjoint_left.mp (colorFamily_disjoint p B5 c e hz hn) hE (hh.symm ▸ hF)
  let eu : globalFamily p B5 c.z (sourceU e) := ⟨Eu,sourceU e,by simp [colors],hEu⟩
  let ezu : globalFamily p B5 c.z (sourceU e) := ⟨Ezu,c.z*sourceU e,by simp [colors],hEzu⟩
  have hVI := pairSpan_le_sourceI p B5 c e hz
  have hmarks := source_marks_mem c e hz
  have hB0 : B5Image B5≤p.F₁ B5 := by
    rw [←hfive]
    rintro x ⟨a,_,rfl⟩
    exact (e a).property
  obtain ⟨hu,hI⟩ := source_inverter c B5 e hz hfive
  have hcards := source_three_fives c B5 (sourceU e) hu
    (PathTransport.source_fusion q c e f hleft hz) hI
  refine ⟨eu,ezu,hEu,hEzu,hBu,hBzu,?_,?_,?_⟩
  · intro hh
    exact hd _ _ huzu Eu Ezu hEu hEzu (congrArg Subtype.val hh)
  · apply (sourceGraph_adj_iff p B5 c.z (sourceU e) _ _).mpr
    exact ⟨hd _ _ hne _ _ hbase hEu,B5Image B5,fixedFive B5 (sourceU e),hB0,hBu,
      B5Image_card d.card_Z B5,hcards.1,hVI.trans (sourceI_le_normalizer B5 e hfive),
      hVI.trans (sourceI_normalizes_fixed B5 e hfive _ hmarks.2),central_edge B5 _⟩
  · apply (sourceGraph_adj_iff p B5 c.z (sourceU e) _ _).mpr
    exact ⟨hd _ _ hzzu _ _ hbase hEzu,B5Image B5,fixedFive B5 (c.z*sourceU e),hB0,hBzu,
      B5Image_card d.card_Z B5,hcards.2.1,hVI.trans (sourceI_le_normalizer B5 e hfive),
      hVI.trans (sourceI_normalizes_fixed B5 e hfive _ ((sourceI e).mul_mem hmarks.1 hmarks.2)),
      central_edge B5 _⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
