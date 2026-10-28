module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSolvableCriticalCommuting
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedDihedralExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedSmallAlphaExclusions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration

/-!
# Removing the reduced D10 actor in the mixed field-four branch

At distance one a critical pair is an edge. Transporting the two original
endpoint markings to that edge makes the D10 actor either alpha or beta.
The alpha index-two obstruction excludes the first orientation, while the
proved field-four/dihedral exclusion excludes the second. The common Borel
and endpoint Sylow premises are supplied by the actual F.1.1 reduction.

An original D10 marking may enlarge to Sz(2). Consequently the original
small-solvable/field-four pair is reduced to a genuine Sz(2) graph actor;
this module does not identify that remaining case with D10 or exclude it.
No path-transitivity or marked-amalgam-recognition premise is introduced.

Source: DGS, Groups and Graphs (1985), 6.1 and its remark, pp.118--119,
and (11.3), (11.5)--(11.7), pp.168--175; Aschbacher--Smith F.1.9--12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
open CommutingNontrivial CommutingOneProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => Reduction.reducedFamily L S

private theorem quotient_at_vertex (h : HypothesisF11 L S)
    {D : Type*} [Group D] (i : Bool)
    (e : (graphLocalGroup F (base F i) ⧸ pCore 2 (graphLocalGroup F (base F i))) ≃* D)
    (v : Vertex F) (hv : v.type = i) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* D) := by
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  obtain ⟨_,f,_,_,_⟩ := CommutingTrivial.local_quotient_parameter_transport
    (Reduction.reduced_triple h) g hg
  exact ⟨f.symm.trans e⟩

/-- For the literal mixed source pair at distance one, its reduced
small-solvable actor cannot retain the D10 quotient. Both orientations of
the attained critical edge are discharged. -/
theorem small_solvable_linear_four_reduced_dihedral_exclusion
    (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (hb : b F = 1)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (eD : (graphLocalGroup F (base F false) ⧸
      pCore 2 (graphLocalGroup F (base F false))) ≃* DihedralGroup 5) : False := by
  have ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  have mark (v : Vertex F) (hv : v.type = true) :
      ClassicalGroup.IsPSL (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) 2 4 :=
    ⟨K,inferInstance,inferInstance,hK,
      quotient_at_vertex h true (Reduction.reduced_graphLinearQuotient h true e) v hv⟩
  have dihedral (v : Vertex F) (hv : v.type = false) :
      Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* DihedralGroup 5) :=
    quotient_at_vertex h false eD v hv
  have hpair : ∃ a beta : Vertex F, IsCriticalPair F a beta :=
    source_exists_criticalPair ht
  obtain ⟨a,beta,hc⟩ := hpair
  have hadj := source_critical_one_adjacent hc hb
  have hcomm := Reduction.reduced_critical_commuting_of_small_solvable h false hm hc
  by_cases ha : a.type = true
  · have hbeta : beta.type = false := by
      have hn := hadj.1
      rw [ha] at hn
      cases he : beta.type <;> simp_all
    exact reduced_linear_four_dihedral_exclusion h d hc hb hcomm
      (mark a ha) (dihedral beta hbeta).some
  · have ha' : a.type = false := Bool.eq_false_iff.mpr ha
    have hbeta : beta.type = true := by
      have hn := hadj.1
      rw [ha'] at hn
      cases he : beta.type <;> simp_all
    have hval : 3 ≤ Nat.card ((graph F).neighborSet beta) := by
      rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index)
        (fun _ => rfl)]
      exact source_valence_ge_three ht (Reduction.reduced_vertex_sylow h) beta.type
    obtain ⟨c,hbc,hca⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet beta)
      (by rw [←Nat.card_coe_set_eq]; omega) a
    have hbmodel : ClassicalGroup.IsPSL (d.localGroup beta ⧸
        pCore 2 (d.localGroup beta)) 2 (2 ^ 2) := mark beta hbeta
    exact reduced_alpha_dihedral_exclusion h d hc hb hcomm hbc hca.symm
      (.linear 2 (by decide) hbmodel) (dihedral a ha').some

/-- The original small-solvable/field-four pair at distance one has a
literal Sz(2) quotient on its reduced small actor. This retains the strict
D10-to-Sz(2) enlargement instead of silently discarding it. -/
theorem small_solvable_linear_four_reduced_suzuki
    (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (hb : b F = 1)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    Nonempty ((graphLocalGroup F (base F false) ⧸
      pCore 2 (graphLocalGroup F (base F false))) ≃* SuzukiMatrixGroup 0) := by
  rcases hm with hd | hs
  · rcases Reduction.reduced_graph_dihedral_alternatives h false hd.some with hD | hSuz
    · exact (small_solvable_linear_four_reduced_dihedral_exclusion h (Or.inl hd) hb hK e
        hD.2.some).elim
    · exact hSuz
  · exact ⟨Reduction.reduced_graphSuzukiQuotient_all h false 0 hs.some⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
