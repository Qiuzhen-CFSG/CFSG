module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableA5CriticalOrientation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableLinearFourDihedral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableLinearFourDistance
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FullCoreShortPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SuzukiShortExclusion

/-!
# Excluding the original small-solvable / A₅ pair at distance one

The directed critical edge starts at the A₅ actor. The small original
quotient enlarges to Sz(2), since the actual D₁₀ actor has been excluded.
The linear alpha marking gives the full adjacent-core product. Both actual
local actions are non-dihedral, so this product gives three-walk transitivity.
The short Suzuki argument then makes a cyclic Suzuki Sylow elementary,
a contradiction.

All local markings, the directed critical edge, the full core product and
the path action are constructed from the original F.1.1 pair. No recognition,
escape or transitivity premise is added. The Chapter 15 wreath-five consumer
supplies the critical distance and applies this exclusion to its literal
faithful completion.
Source: DGS, *Groups and Graphs* (1985), (11.4)--(11.8), pp.171--176;
Aschbacher--Smith 15.2.4--8, printed pp.1106--1110.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
open CommutingNontrivial CommutingOneProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => Reduction.reducedFamily L S

/-- The original D₁₀-or-Sz(2) / A₅ pair is impossible at critical distance
one. Every local, orientation, escape and path premise is discharged. -/
theorem small_solvable_a5_distance_one_exclusion (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (ha : Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* alternatingGroup (Fin 5)))
    (hb : b F = 1) : False := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let a : Vertex F := base F true
  let beta : Vertex F := base F false
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hK
  let e := ha.some.trans e₄.symm
  let ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,GaloisField 2 2) :=
    (linear_graph_quotient h true e a rfl).some
  let eb : (d.localGroup beta ⧸ pCore 2 (d.localGroup beta)) ≃* SuzukiMatrixGroup 0 :=
    (small_solvable_linear_four_reduced_suzuki h hm hb hK e).some
  obtain ⟨hc,hcomm⟩ := small_solvable_a5_base_critical h hm ha hb
  have hab : (graph F).Adj a beta := SimpleGraph.dist_eq_one_iff_adj.mp (hc.1.trans hb)
  have models (v : Vertex F) : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)) :=
    small_solvable_a5_graph_models h hm ha v
  have hnot (v : Vertex F) :
      ¬ Nonempty ((d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* DihedralGroup 5) := by
    rintro ⟨ev⟩
    by_cases hv : v.type = true
    · let eA := (a5_graph_quotient h true ha.some v hv).some
      have he := Nat.card_congr (eA.symm.trans ev).toEquiv
      rw [nat_card_alternatingGroup,DihedralGroup.nat_card] at he
      norm_num [Nat.factorial] at he
    · have hv' : v.type = false := Bool.eq_false_iff.mpr hv
      obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
      rw [hv'] at hg
      obtain ⟨_,f,_,_,_⟩ := CommutingTrivial.local_quotient_parameter_transport ht g hg
      let eS := f.symm.trans eb
      have he := Nat.card_congr (eS.symm.trans ev).toEquiv
      rw [suzukiZero_card,DihedralGroup.nat_card] at he
      norm_num at he
  have hval : 3 ≤ Nat.card ((graph F).neighborSet beta) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three ht (Reduction.reduced_vertex_sylow h) beta.type
  obtain ⟨c,hbc,hca⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet beta)
    (by rw [←Nat.card_coe_set_eq]; omega) a
  have hprod := (source_linear_rankOne_core_identities ht (Reduction.reduced_borel_core_sylow h)
    d hc hb hbc hca.symm (models a) (models beta) ea).1
  have hthree := source_three_walk_transitive_of_full_core_product ht
    (Reduction.reduced_borel_core_sylow h) d hab hprod models hnot
  exact source_linear_suzuki_exclusion_of_three_walks ht (Reduction.reduced_borel_core_sylow h)
    (Reduction.reduced_vertex_sylow h) d hc hb hcomm (models a) ea 0 eb hprod hthree

/-- The original small-solvable / A₅ F.1.1 pair is impossible. Its quotient
orders are below 72 and its unequal local parameters force critical distance
one, so the source pair needs no additional distance hypothesis. -/
theorem small_solvable_a5_exclusion (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (ha : Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* alternatingGroup (Fin 5))) : False := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hK
  apply small_solvable_a5_distance_one_exclusion h hm ha
  apply small_solvable_linear_four_distance_one h hm ?_ hK (ha.some.trans e₄.symm)
  intro i
  fin_cases i
  · change Nat.card (L 0 ⧸ pCore 2 (L 0)) < 72
    rcases hm with hm | hm
    · rw [Nat.card_congr hm.some.toEquiv,DihedralGroup.nat_card]
      norm_num
    · rw [Nat.card_congr hm.some.toEquiv,suzukiZero_card]
      norm_num
  · change Nat.card (L 1 ⧸ pCore 2 (L 1)) < 72
    rw [Nat.card_congr ha.some.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
