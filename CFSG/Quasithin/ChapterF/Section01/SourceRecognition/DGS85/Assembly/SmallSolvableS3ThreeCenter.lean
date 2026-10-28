module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableS3Markings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.KernelControl

/-!
# The original S₃ endpoint in the nonzero commuting branch

For an original D₁₀-or-Sz(2) / S₃ pair, the moving-neighbor catalogue
discharges central displacement. DGS 8.6 makes the starting center natural.
Its quotient has order divisible by three, so the starting vertex is on the
S₃ orbit. The adjacent center is central and DGS 8.1 kills the starting
local center. Conjugation and the literal linear actor equivalence carry
this conclusion to the original second factor when its full parabolic is
that factor itself.

Consequently a nontrivial original second-factor center forces distance one.
The center premise is essential: the uncentered mixed pairs occur in the
Ree and Tits models. The Chapter 15 application supplies a central involution
in the actual H-star, not in an abstract replacement or a smaller subgroup.
Source: DGS, *Groups and Graphs* (1985), 8.1, 8.6 and 12.1;
Aschbacher--Smith 15.2.8, printed pp.1109--1110.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
open CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => Reduction.reducedFamily L S

private theorem small_solvable_not_natural (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (a : Vertex F) (ha : a.type = false) :
    ¬ Noncommuting.HasNaturalCenter (graphLocalGroup F a) (Z F a) (Q F a) := by
  intro hn
  obtain ⟨K,hK,hfin,hchar,⟨e⟩⟩ := source_natural_center_linear_quotient
    (Reduction.reduced_triple h) (Reduction.reducedFullEarlierLocalTheorems h) a hn
  let := hK
  let := hfin
  let := hchar
  have hd : 3 ∣ Nat.card (graphLocalGroup F a ⧸ pCore 2 (graphLocalGroup F a)) := by
    have he : Nat.card (graphLocalGroup F a ⧸ pCore 2 (graphLocalGroup F a)) =
        Nat.card PSL(2,K) := Nat.card_congr
      (e.trans (Theory.PSL2.sl2QuotientEquiv K)).toEquiv
    rw [he]
    exact three_dvd_card_psl2_char_two K
  rcases small_solvable_graph_quotients h false hm a ha with hD | hSuz
  · rw [Nat.card_congr hD.some.toEquiv,DihedralGroup.nat_card] at hd
    norm_num at hd
  · rw [Nat.card_congr hSuz.some.toEquiv,suzukiZero_card] at hd
    norm_num at hd

/-- Nonzero commuting displacement makes the actual original S₃ factor
centerless, provided this factor is its own full parabolic. -/
theorem small_solvable_s3_original_center_eq_bot
    (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (hs : Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* Equiv.Perm (Fin 3)))
    (hP : parabolic L S 1 = L 1)
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F)
    (hb : 1 < b F) (hcomm : ⁅Z F a,Z F a'⁆ = ⊥)
    (hne : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≠ ⊥) : center (L 1) = ⊥ := by
  have ht := Reduction.reduced_triple h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : ∀ v : Vertex F, Finite (graphLocalGroup F v) := fun v => Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have models := small_solvable_s3_graph_models h hm hs
  obtain ⟨w,hw,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  have hcentral : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≤ Z F a' := by
    by_cases hwtype : w.val.type = true
    · exact reduced_linear_moving_commutator_central h models hc hab hd hb hcomm w hw
        ((symmetricThree_graph_quotient h true hs.some w.val hwtype).some.trans
          SLTwoPermThree.sl2Two_equiv_perm_three.some.symm)
    · rcases small_solvable_graph_quotients h false hm w.val
        (Bool.eq_false_iff.mpr hwtype) with hd' | hz
      · exact reduced_dihedral_moving_commutator_central h models hc hab hd hb hcomm w hw hd'.some
      · exact (reduced_suzuki_all_moving_commutator_central h models hc hab hd hb hcomm
          w hw 0 hz.some).le
  obtain ⟨_,mid,_,_,hAD,hDI,hIN,_⟩ :=
    reduced_critical_central_equivalences h models hc hab hd hb hcomm hne
  have hnat := hIN.mp (hDI.mp (hAD.mp hcentral))
  have hatype : a.type = true := by
    by_contra hn
    exact small_solvable_not_natural h hm a (Bool.eq_false_iff.mpr hn) hnat
  have hneighbor := (reduced_critical_geometry h
    (Reduction.reducedFullEarlierLocalTheorems h) hc hab hd hb hcomm).2.2.1
  have hz : center (graphLocalGroup F a) = ⊥ :=
    local_center_eq_bot_of_neighbor_central ht
      (Reduction.reducedFullEarlierLocalTheorems h) hab hneighbor
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F a
  rw [hatype] at hg
  obtain ⟨eg,_,_,_,_⟩ := CommutingTrivial.local_quotient_parameter_transport ht g hg
  let eP := (hs.some.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm).trans
    (Theory.PSL2.sl2QuotientEquiv (ZMod 2))
  have hstar : family (starredParabolic L S) true = L 1 := by
    change starredParabolic L S 1 = L 1
    exact le_antisymm ((starredParabolic_le 1).trans_eq hP) (local_le_starredParabolic 1)
  let ebase : graphLocalGroup F (base F true) ≃* L 1 :=
    (Reduction.reduced_linearActorEquiv h true eP).trans (MulEquiv.subgroupCongr hstar)
  let ea : L 1 ≃* graphLocalGroup F a := ebase.symm.trans eg
  apply bot_unique
  intro z hz'
  have he : ea z ∈ center (graphLocalGroup F a) :=
    (MulEquivClass.apply_mem_center_iff ea).mpr hz'
  rw [hz,mem_bot] at he
  exact mem_bot.mpr (ea.injective (he.trans (map_one ea).symm))

/-- A nontrivial center in the original full S₃ endpoint rules out the
nonzero distance-three branch and forces distance one. -/
theorem small_solvable_s3_distance_one_of_original_center
    (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (hs : Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* Equiv.Perm (Fin 3)))
    (hP : parabolic L S 1 = L 1) (hz : center (L 1) ≠ ⊥) : b F = 1 := by
  have ht := Reduction.reduced_triple h
  have hpair : ∃ a a' : Vertex F, IsCriticalPair F a a' := source_exists_criticalPair ht
  obtain ⟨a,a',hc⟩ := hpair
  have hne : a' ≠ a := by
    intro he
    have hp : 0 < b F := source_b_positive ht
    have hd := hc.1
    rw [he,SimpleGraph.dist_self] at hd
    omega
  obtain ⟨beta,hab,hd⟩ := exists_predecessor F ht.generate a' a hne
  rw [SimpleGraph.dist_comm (u := a') (v := beta),
    SimpleGraph.dist_comm (u := a') (v := a),hc.1] at hd
  have hcard (i : Fin 2) : Nat.card (L i ⧸ pCore 2 (L i)) < 72 := by
    fin_cases i
    · change Nat.card (L 0 ⧸ pCore 2 (L 0)) < 72
      rcases hm with hm | hm
      · rw [Nat.card_congr hm.some.toEquiv,DihedralGroup.nat_card]
        norm_num
      · rw [Nat.card_congr hm.some.toEquiv,suzukiZero_card]
        norm_num
    · change Nat.card (L 1 ⧸ pCore 2 (L 1)) < 72
      rw [Nat.card_congr hs.some.toEquiv,Nat.card_perm,Nat.card_fin]
      norm_num
  obtain ⟨hcomm,hb⟩ := reduced_small_solvable_critical_alternatives h false hm hcard hc hab hd
  rcases hb with hb | ⟨hb,hdn⟩
  · exact hb
  · exact (hz (small_solvable_s3_original_center_eq_bot h hm hs hP hc hab hd
      (by omega) hcomm hdn)).elim

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
