module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Triangle
public import Theory.GroupAction.MaximalCosetOrbit

/-!
# The two marked stabilizers in the seventeen-point action

The pointwise stabilizer of the two source cosets is the literal
intersection H₁ ∩ H₂. Adjoining the outside involution recovers H₂,
which is therefore exactly the setwise pair stabilizer. Lemma 2.7's
faithful action thus carries both markings required by Lemma 2.9.
This module does not assert uniqueness of these embeddings.

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Lemmas 2.7 and 2.9, printed pp.497–498.
-/

public noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Janko3.SourceRecognition.Seventeen.SourceData
variable {G : Type*} [Group G] (S : SourceData G)

theorem pointwise_pair_stabilizer
    (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1) (hb2 : b ∈ S.H2) :
    let D := S.cosetData b hb hbout
    stabilizer G (CosetGraph.base D) ⊓ stabilizer G (CosetGraph.other D) = S.H1 ⊓ S.H2 := by
  let D := S.cosetData b hb hbout
  have he := S.edge_stabilizer b hb hbout hb2
  change stabilizer G (CosetGraph.base D) ⊓ stabilizer G (CosetGraph.other D) = S.H1 ⊓ S.H2
  rw [CosetGraph.point_stabilizer]
  ext g
  constructor
  · rintro ⟨hg, hh⟩
    have hm : (⟨g, hg⟩ : S.H1) ∈ CosetGraph.edgeStabilizer D := hh
    rw [he] at hm
    exact ⟨hg, hm⟩
  · rintro ⟨hg, hh⟩
    refine ⟨hg, ?_⟩
    have hm : (⟨g, hg⟩ : S.H1) ∈ S.H2.subgroupOf S.H1 := hh
    rw [← he] at hm
    exact hm

theorem pair_generated (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1) (hb2 : b ∈ S.H2) :
    (S.H1 ⊓ S.H2) ⊔ zpowers b = S.H2 := by
  apply le_antisymm (sup_le inf_le_right (zpowers_le.mpr hb2))
  intro x hx
  by_cases h1 : x ∈ S.H1
  · exact (show S.H1 ⊓ S.H2 ≤ (S.H1 ⊓ S.H2) ⊔ zpowers b from le_sup_left) ⟨h1, hx⟩
  · have hm : (⟨b, hb2⟩ : S.H2) * ⟨x, hx⟩ ∈ S.H1.subgroupOf S.H2 := by
      rw [mul_mem_iff_of_index_two S.overlap_index_two]
      exact iff_of_false hbout h1
    have hh : b * x ∈ S.H1 ⊓ S.H2 := ⟨hm, S.H2.mul_mem hb2 hx⟩
    have hbb : b ∈ (S.H1 ⊓ S.H2) ⊔ zpowers b :=
      (show zpowers b ≤ (S.H1 ⊓ S.H2) ⊔ zpowers b from le_sup_right) (mem_zpowers b)
    have hxx := ((S.H1 ⊓ S.H2) ⊔ zpowers b).mul_mem hbb
      ((show S.H1 ⊓ S.H2 ≤ (S.H1 ⊓ S.H2) ⊔ zpowers b from le_sup_left) hh)
    simpa only [← mul_assoc, hb, one_mul] using hxx

/-- H₂ is exactly the setwise stabilizer of the two source cosets. -/
theorem setwise_pair_stabilizer
    (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1) (hb2 : b ∈ S.H2) :
    let D := S.cosetData b hb hbout
    stabilizer G ({CosetGraph.base D, CosetGraph.other D} : Set (CosetGraph.Vertex D)) = S.H2 := by
  let D := S.cosetData b hb hbout
  change stabilizer G ({CosetGraph.base D, CosetGraph.other D} : Set (CosetGraph.Vertex D)) = S.H2
  rw [stabilizer_pair_eq_sup (CosetGraph.swap_base D) (CosetGraph.swap_other D),
    S.pointwise_pair_stabilizer b hb hbout hb2]
  exact S.pair_generated b hb hbout hb2

/-- The action used in Lemma 2.9 retains both distinguished stabilizers. -/
theorem exists_marked_action :
    ∃ (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1), b ∈ S.H2 ∧ b ∈ S.H3 ∧
      let D := S.cosetData b hb hbout
      FaithfulSMul G (CosetGraph.Vertex D) ∧
        IsMultiplyPretransitive G (CosetGraph.Vertex D) 3 ∧
        Nat.card (CosetGraph.Vertex D) = 17 ∧
        stabilizer G (CosetGraph.base D) = S.H1 ∧
        stabilizer G ({CosetGraph.base D, CosetGraph.other D} : Set (CosetGraph.Vertex D)) = S.H2 := by
  obtain ⟨b, hb, hb2, hb3, hout⟩ := S.exists_outside_involution
  obtain ⟨hf, _, _, _, hc, ht, _⟩ := S.consequences b hb hout hb2 hb3
  exact ⟨b, hb, hout, hb2, hb3, hf, ht, hc, CosetGraph.point_stabilizer _,
    S.setwise_pair_stabilizer b hb hout hb2⟩

end Sporadic.Janko3.SourceRecognition.Seventeen.SourceData
