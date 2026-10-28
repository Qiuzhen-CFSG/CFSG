module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableCriticalAlternatives
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LinearMovingCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.SuzukiMovingCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.AdjacentParameterEquality

/-!
# Distance one for the small-solvable / linear-four pair

An original D₁₀ or Sz(2) endpoint forces commuting critical pairs. The
small-quotient alternatives leave only distance one or nonzero displacement
at distance three. In the latter case every possible moving neighbor has
central displacement, so DGS 8.6 makes the starting center natural. Its
quotient cannot be D₁₀ or Sz(2), whose order is prime to three. It therefore
has the actual linear-four marking. DGS 8.7 then identifies its quotient
Sylow omega order, four, with the adjacent small-solvable order, at most two.

The proof uses the literal original quotient markings and all-parameter
Suzuki centrality. The Chapter 15 wreath mixed-pair consumer discharges the
quotient order bound. Distance-one recognition remains a separate obligation.
Source: DGS, *Groups and Graphs* (1985), Theorem B, 8.6--8.7 and 9.10;
Aschbacher--Smith 15.2.4--8, printed pp.1106--1110.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
open CommutingNontrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => Reduction.reducedFamily L S

private theorem small_graph_quotients (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (v : Vertex F) (hv : v.type = false) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* DihedralGroup 5) ∨
      Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SuzukiMatrixGroup 0) := by
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  obtain ⟨_,f,_,_,_⟩ := CommutingTrivial.local_quotient_parameter_transport
    (Reduction.reduced_triple h) g hg
  rcases hm with hm | hm
  · rcases Reduction.reduced_graph_dihedral_alternatives h false hm.some with hd | hs
    · exact Or.inl ⟨f.symm.trans hd.2.some⟩
    · exact Or.inr ⟨f.symm.trans hs.some⟩
  · exact Or.inr ⟨f.symm.trans (Reduction.reduced_graphSuzukiQuotient_all h false 0 hm.some)⟩

private theorem linear_graph_quotient (h : HypothesisF11 L S)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (v : Vertex F) (hv : v.type = true) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K)) := by
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  obtain ⟨_,f,_,_,_⟩ := CommutingTrivial.local_quotient_parameter_transport
    (Reduction.reduced_triple h) g hg
  exact ⟨f.symm.trans ((Reduction.reduced_graphLinearQuotient h true e).trans
    (Theory.PSL2.sl2QuotientEquiv K).symm)⟩

private theorem small_not_natural (h : HypothesisF11 L S)
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
  rcases small_graph_quotients h hm a ha with hD | hSuz
  · rw [Nat.card_congr hD.some.toEquiv,DihedralGroup.nat_card] at hd
    norm_num at hd
  · rw [Nat.card_congr hSuz.some.toEquiv,suzukiZero_card] at hd
    norm_num at hd

private theorem omega_card_equiv {D E : Type*} [Group D] [Finite D] [Group E]
    (e : D ≃* E) (T : Sylow 2 D) :
    Nat.card (omegaCenterIn (T : Subgroup D)) =
      Nat.card (omegaCenterIn (T.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup E)) := by
  change Nat.card (omegaCenterIn (T : Subgroup D)) =
    Nat.card (omegaCenterIn ((T : Subgroup D).map e.toMonoidHom))
  rw [←NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective]
  exact (card_map_of_injective (K := omegaCenterIn (T : Subgroup D))
    (f := e.toMonoidHom) e.injective).symm

/-- Unequal actual omega parameters exclude the distance-three branch of
the small-solvable/linear-four pair. -/
private theorem small_solvable_linear_four_critical_distance_one
    (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (hcard : ∀ i, Nat.card (L i ⧸ pCore 2 (L i)) < 72)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F) : b F = 1 := by
  have ht := Reduction.reduced_triple h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : ∀ v : Vertex F, Finite (graphLocalGroup F v) := fun v => Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have models (v : Vertex F) : IsRankOneModel (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) := by
    by_cases hv : v.type = true
    · exact .linear 2 (by decide) ⟨K,inferInstance,inferInstance,(by simpa using hK),
        ⟨(linear_graph_quotient h e v hv).some.trans (Theory.PSL2.sl2QuotientEquiv K)⟩⟩
    · have hv' : v.type = false := Bool.eq_false_iff.mpr hv
      rcases small_graph_quotients h hm v hv' with hd | hs
      · exact .dihedral hd
      · exact .suzuki 0 hs
  obtain ⟨hcomm,hb⟩ := reduced_small_solvable_critical_alternatives h false hm hcard hc hab hd
  rcases hb with hb | ⟨hb,hne⟩
  · exact hb
  exfalso
  have hb' : 1 < b F := by omega
  obtain ⟨w,hw,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  have hcentral : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≤ Z F a' := by
    by_cases hwtype : w.val.type = true
    · exact reduced_linear_moving_commutator_central h models hc hab hd hb' hcomm w hw
        (linear_graph_quotient h e w.val hwtype).some
    · rcases small_graph_quotients h hm w.val (Bool.eq_false_iff.mpr hwtype) with hd' | hs
      · exact reduced_dihedral_moving_commutator_central h models hc hab hd hb' hcomm w hw hd'.some
      · exact (reduced_suzuki_all_moving_commutator_central h models hc hab hd hb' hcomm w hw 0 hs.some).le
  obtain ⟨_,mid,_,_,hAD,hDI,hIN,_⟩ := reduced_critical_central_equivalences h models hc hab hd hb' hcomm hne
  have hnat := hIN.mp (hDI.mp (hAD.mp hcentral))
  have hatype : a.type = true := by
    by_contra hn
    exact small_not_natural h hm a (Bool.eq_false_iff.mpr hn) hnat
  have hbtype : beta.type = false := by
    have hn := hab.1
    rw [hatype] at hn
    cases he : beta.type <;> simp_all
  let Rα : Sylow 2 (graphLocalGroup F a) := default
  let Rβ : Sylow 2 (graphLocalGroup F beta) := default
  have heq := reduced_natural_start_adjacent_parameter_equality h models hc hab hd hb' hcomm hne hnat Rα Rβ
  have hfour := (CommutingTrivial.linear_marking_quotient_sylow_omega_card
    (linear_graph_quotient h e a hatype).some Rα).trans hK
  rw [hfour] at heq
  let T := Rβ.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup F beta)))
  have hsmall : Nat.card (omegaCenterIn T.toSubgroup) ≤ 2 := by
    rcases small_graph_quotients h hm beta hbtype with hd' | hs
    · let eD := hd'.some
      let U := T.mapSurjective (f := eD.toMonoidHom) eD.surjective
      have hU : Nat.card U = 2 := by
        rw [U.card_eq_multiplicity,DihedralGroup.nat_card]
        decide +kernel
      exact ((omega_card_equiv eD T).le.trans (card_le_of_le (map_subtype_le _))).trans_eq hU
    · have he := (omega_card_equiv hs.some T).trans (suzukiSylow_omegaCenter_card_index 0 _).1
      change Nat.card (omegaCenterIn T.toSubgroup) = 2 at he
      exact he.le
  change 4 = Nat.card (omegaCenterIn T.toSubgroup) at heq
  omega

/-- A small-solvable/linear-four pair has critical distance one. -/
theorem small_solvable_linear_four_distance_one
    (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (hcard : ∀ i, Nat.card (L i ⧸ pCore 2 (L i)) < 72)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) : b F = 1 := by
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
  apply small_solvable_linear_four_critical_distance_one h hm hcard hK e hc hab
  rw [SimpleGraph.dist_comm (u := a') (v := beta),
    SimpleGraph.dist_comm (u := a') (v := a),hc.1] at hd
  exact hd

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
