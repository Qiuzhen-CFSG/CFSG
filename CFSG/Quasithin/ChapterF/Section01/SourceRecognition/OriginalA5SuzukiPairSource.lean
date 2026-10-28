module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.OriginalSuzukiCriticalSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableLinearFourMarkings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.CommutingTrivialChapterEightSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceSuzukiExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearBetaSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LinearMovingCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.SuzukiMovingCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.AdjacentParameterEquality

/-!
# Excluding an original alternating-five / Suzuki F.1.1 pair

The literal quotient markings determine both graph-actor orbits. The Suzuki
endpoint rules out noncommuting critical pairs. At distance one, intrinsic
source selection excludes a Suzuki beta actor and makes the alpha actor
linear when beta is alternating five.

For longer commuting pairs, zero displacement gives linear actors on both
orbits. Nonzero displacement is central for either possible moving actor,
so the starting center is natural. Its actor is therefore the alternating-five
one. The adjacent quotient Sylow omega orders must agree, contradicting their
actual orders four and 2^(2m+1), with m positive.

All critical pairs, moving neighbors, local markings and naturality witnesses
are constructed from the original F.1.1 pair. The whole input Sylow subgroup
is retained, with no normalized-Borel or recognition assumption.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open CommutingNontrivial CommutingOneProfile

variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily J S

private theorem field_four_card : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by decide)]
  norm_num

private theorem a5_linear_marking (h : HypothesisF11 J S)
    (a : Nonempty ((J 0 ⧸ pCore 2 (J 0)) ≃* alternatingGroup (Fin 5)))
    (v : Vertex F) (hv : v.type = false) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃*
      SL(2,GaloisField 2 2)) := by
  obtain ⟨e4⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    field_four_card
  exact ⟨((Assembly.a5_graph_quotient h false a.some v hv).some.trans e4.symm).trans
    (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).symm⟩

private theorem a5_projective_marking (h : HypothesisF11 J S)
    (a : Nonempty ((J 0 ⧸ pCore 2 (J 0)) ≃* alternatingGroup (Fin 5)))
    (v : Vertex F) (hv : v.type = false) :
    ClassicalGroup.IsPSL (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) 2 (2^2) :=
  ⟨GaloisField 2 2,inferInstance,inferInstance,(by simpa using field_four_card),
    ⟨(a5_linear_marking h a v hv).some.trans (Theory.PSL2.sl2QuotientEquiv _)⟩⟩

private theorem mixed_models (h : HypothesisF11 J S)
    (a : Nonempty ((J 0 ⧸ pCore 2 (J 0)) ≃* alternatingGroup (Fin 5)))
    {m : ℕ} (hm : 0 < m)
    (e : Nonempty ((J 1 ⧸ pCore 2 (J 1)) ≃* SuzukiMatrixGroup m))
    (v : Vertex F) : IsRankOneModel (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) := by
  by_cases hv : v.type = false
  · exact .linear 2 (by decide) (a5_projective_marking h a v hv)
  · exact .suzuki m (original_suzuki_graph_quotient h true hm e.some v
      (by cases hv' : v.type <;> simp_all))

private theorem linear_not_suzuki {H K : Type*} [Group H]
    [Field K] [Finite K] [CharP K 2] {m : ℕ} (hm : 0 < m)
    (e : H ≃* SuzukiMatrixGroup m) (f : H ≃* SL(2,K)) : False :=
  not_nonempty_psl2_char_two_equiv_suzuki K hm
    ⟨(Theory.PSL2.sl2QuotientEquiv K).symm.trans (f.symm.trans e)⟩

private theorem projective_not_suzuki {H : Type*} [Group H] {m n : ℕ}
    (hm : 0 < m) (e : H ≃* SuzukiMatrixGroup m)
    (mark : ClassicalGroup.IsPSL H 2 (2^n)) : False := by
  obtain ⟨K,_,_,hK,⟨f⟩⟩ := mark
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hK)
  exact not_nonempty_psl2_char_two_equiv_suzuki K hm ⟨f.symm.trans e⟩

private theorem mixed_not_distance_one (h : HypothesisF11 J S)
    (a : Nonempty ((J 0 ⧸ pCore 2 (J 0)) ≃* alternatingGroup (Fin 5)))
    {m : ℕ} (hm : 0 < m)
    (e : Nonempty ((J 1 ⧸ pCore 2 (J 1)) ≃* SuzukiMatrixGroup m))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hb : b F = 1)
    (hcomm : ⁅Z F v,Z F w⁆ = ⊥) : False := by
  let ht := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hadj := source_critical_one_adjacent hc hb
  by_cases hw : w.type = true
  · exact source_suzuki_beta_exclusion ht (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) d hc hb hcomm (mixed_models h a hm e v) m
      (original_suzuki_graph_quotient h true hm e.some w hw).some
  · have hw' : w.type = false := Bool.eq_false_iff.mpr hw
    have hv : v.type = true := by
      have hh := hadj.1
      cases hv : v.type <;> simp_all
    have hn := card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl) w
    have hcard : 1 < ((graph F).neighborSet w).ncard := by
      rw [←Nat.card_coe_set_eq,hn]
      have hh := source_valence_ge_three ht (reduced_vertex_sylow h) w.type
      change 3 ≤ ((F (!w.type)).subgroupOf (F w.type)).index at hh
      omega
    obtain ⟨c,hwc,hcv⟩ := Set.exists_ne_of_one_lt_ncard hcard v
    obtain ⟨_,n,_,mark⟩ := source_linear_beta_core_product_and_alpha ht
      (reduced_borel_core_sylow h) d hc hb hcomm hwc hcv.symm
      (mixed_models h a hm e v) (by decide : 0 < 2) (a5_projective_marking h a w hw')
    exact projective_not_suzuki hm
      (original_suzuki_graph_quotient h true hm e.some v hv).some mark

private theorem omega_card_equiv {D E : Type*} [Group D] [Finite D] [Group E]
    (e : D ≃* E) (T : Sylow 2 D) :
    Nat.card (omegaCenterIn (T : Subgroup D)) =
      Nat.card (omegaCenterIn (T.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup E)) := by
  change Nat.card (omegaCenterIn (T : Subgroup D)) =
    Nat.card (omegaCenterIn ((T : Subgroup D).map e.toMonoidHom))
  rw [←NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective]
  exact (card_map_of_injective (K := omegaCenterIn (T : Subgroup D))
    (f := e.toMonoidHom) e.injective).symm

private theorem mixed_longer_false (h : HypothesisF11 J S)
    (a : Nonempty ((J 0 ⧸ pCore 2 (J 0)) ≃* alternatingGroup (Fin 5)))
    {m : ℕ} (hm : 0 < m)
    (e : Nonempty ((J 1 ⧸ pCore 2 (J 1)) ≃* SuzukiMatrixGroup m))
    {v beta w : Vertex F} (hc : IsCriticalPair F v w) (hab : (graph F).Adj v beta)
    (hd : (graph F).dist beta w + 1 = b F) (hb : 1 < b F)
    (hcomm : ⁅Z F v,Z F w⁆ = ⊥) : False := by
  let ht := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : ∀ z : Vertex F, Finite (graphLocalGroup F z) := fun z => Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have models := mixed_models h a hm e
  by_cases htriv : ⁅V F beta 1 ⊓ Q F w,V F w 1⁆ = ⊥
  · obtain ⟨_,K,_,_,_,E,_,_,_,_,_,⟨fβ⟩,⟨fv⟩⟩ :=
      CommutingTrivial.reduced_critical_fields_two_from_chapterEight
        h models hc hab hd hb hcomm htriv
    by_cases hv : v.type = true
    · exact linear_not_suzuki hm
        (original_suzuki_graph_quotient h true hm e.some v hv).some fv
    · have hβ : beta.type = true := by
        have hh := hab.1
        cases hv' : v.type <;> cases hβ : beta.type <;> simp_all
      exact linear_not_suzuki hm
        (original_suzuki_graph_quotient h true hm e.some beta hβ).some fβ
  · obtain ⟨z,hz,_⟩ := exists_moving_neighbor F (fun x => (source_Z_Q_U ht x).1) beta w htriv
    have hcentral : ⁅V F beta 1 ⊓ Q F w,V F w 1⁆ ≤ Z F w := by
      by_cases hztype : z.val.type = false
      · exact reduced_linear_moving_commutator_central h models hc hab hd hb hcomm z hz
          (a5_linear_marking h a z.val hztype).some
      · exact (reduced_suzuki_all_moving_commutator_central h models hc hab hd hb hcomm z hz m
          (original_suzuki_graph_quotient h true hm e.some z.val
            (by cases hz' : z.val.type <;> simp_all)).some).le
    obtain ⟨_,mid,_,_,hAD,hDI,hIN,_⟩ :=
      reduced_critical_central_equivalences h models hc hab hd hb hcomm htriv
    have hnat := hIN.mp (hDI.mp (hAD.mp hcentral))
    have hv : v.type = false := by
      by_contra hv
      obtain ⟨K,_,_,_,⟨f⟩⟩ := source_natural_center_linear_quotient ht d v hnat
      exact linear_not_suzuki hm
        (original_suzuki_graph_quotient h true hm e.some v
          (by cases hv' : v.type <;> simp_all)).some f
    have hβ : beta.type = true := by
      have hh := hab.1
      cases hβ : beta.type <;> simp_all
    let Rv : Sylow 2 (graphLocalGroup F v) := default
    let Rβ : Sylow 2 (graphLocalGroup F beta) := default
    have heq := reduced_natural_start_adjacent_parameter_equality
      h models hc hab hd hb hcomm htriv hnat Rv Rβ
    have hfour := (CommutingTrivial.linear_marking_quotient_sylow_omega_card
      (a5_linear_marking h a v hv).some Rv).trans field_four_card
    rw [hfour] at heq
    let T := Rβ.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup F beta)))
    have hs := (omega_card_equiv (original_suzuki_graph_quotient h true hm e.some beta hβ).some T).trans
      (suzukiSylow_omegaCenter_card_index m _).1
    change 4 = Nat.card (omegaCenterIn T.toSubgroup) at heq
    have hlarge : 8 ≤ 2^(2*m+1) := by
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
        (show 3 ≤ 2*m+1 by omega)
      norm_num at hh
      exact hh
    omega

/-- An original F.1.1 pair cannot have an alternating-five quotient on one
endpoint and a positive-parameter Suzuki quotient on the other. -/
theorem original_a5_suzuki_pair_false {L A : Subgroup G}
    (h : HypothesisF11 ![L,A] S)
    (a : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {m : ℕ} (hm : 0 < m)
    (e : Nonempty ((A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup m)) : False := by
  let J : Fin 2 → Subgroup G := ![L,A]
  let Γ := reducedFamily J S
  have ht := reduced_triple h
  obtain ⟨v,w,hc⟩ := reduced_criticalPair h
  have hp : 0 < b Γ := source_b_positive ht
  have hne : w ≠ v := by
    intro he
    have hh := hc.1
    change (graph Γ).dist v w = b Γ at hh
    rw [he,SimpleGraph.dist_self] at hh
    omega
  obtain ⟨beta,hab,hd⟩ := exists_predecessor Γ ht.generate w v hne
  rw [SimpleGraph.dist_comm (u := w) (v := beta),
    SimpleGraph.dist_comm (u := w) (v := v),hc.1] at hd
  have hcomm := original_suzuki_critical_centers_commute h true hm e.some hc
  by_cases hb : b Γ = 1
  · exact mixed_not_distance_one h a hm e hc hb hcomm
  · have hlong : 1 < b Γ := by omega
    exact mixed_longer_false h a hm e hc hab hd hlong hcomm

end CFSG.Quasithin.ChapterF.Source
