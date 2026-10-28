module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NaturalNeighborCenter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LinearMovingCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.CommutingTrivialChapterEightSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableLinearFourMarkings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallUnitarySolvability

/-!
# The full opposite center in a long commuting original A5 pair

In the reverse orientation the critical actor has trivial center. In the
forward orientation zero displacement would make the original A5 quotient
binary. Nonzero displacement supplies a moving field-four neighbor, whose
literal action makes the starting center natural. The full opposite center
then has no involution by the natural neighbor calculation.

Only the original left quotient is marked. Nonsolvability of the original
parabolics supplies the retained local catalogue internally.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily J S

private theorem center_involution_eq_one_of_actor_center
    {X : Type*} [Group X] {P : Subgroup X}
    (hc : center (sylowGenerated P) = ⊥)
    (x : X) (hx : x ∈ (center P).map P.subtype) (hx2 : x^2=1) : x=1 := by
  obtain ⟨z,hz,rfl⟩ := hx
  have hp : IsPGroup 2 (zpowers (z : X)) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hx2).isPGroup 2 _
  have hza : (z : X) ∈ sylowGenerated P :=
    pGroup_le_sylowGenerated P _ (zpowers_le.mpr z.property) hp (mem_zpowers _)
  have hzc : (⟨z,hza⟩ : sylowGenerated P) ∈ center (sylowGenerated P) := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact congrArg P.subtype (mem_center_iff.mp hz ⟨y,sylowGenerated_le P y.property⟩)
  have he : (⟨z,hza⟩ : sylowGenerated P) = 1 := by
    apply mem_bot.mp
    rwa [hc] at hzc
  exact congrArg (sylowGenerated P).subtype he

private theorem field_four_card : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by decide)]
  norm_num

private theorem a5_linear_marking (h : HypothesisF11 J S)
    (a : (J 0 ⧸ pCore 2 (J 0)) ≃* alternatingGroup (Fin 5))
    (v : Vertex F) (hv : v.type = false) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃*
      SL(2,GaloisField 2 2)) := by
  obtain ⟨e4⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    field_four_card
  exact ⟨((Assembly.a5_graph_quotient h false a v hv).some.trans e4.symm).trans
    (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).symm⟩

private theorem based_long_center
    (h : HypothesisF11 J S)
    (a : (J 0 ⧸ pCore 2 (J 0)) ≃* alternatingGroup (Fin 5))
    (models : ∀ z : Vertex F,
      IsRankOneModel (graphLocalGroup F z ⧸ pCore 2 (graphLocalGroup F z)))
    (i : Bool) {w : Vertex F}
    (hc : IsCriticalPair F (base F i) w)
    (hd : (graph F).dist (base F (!i)) w + 1 = b F)
    (hb : 1 < b F) (hcomm : ⁅Z F (base F i),Z F w⁆ = ⊥)
    (x : G₀ J S) (hx : x ∈ (center (stabilizer F (base F true))).map
      (stabilizer F (base F true)).subtype) (hx2 : x^2=1) : x=1 := by
  let ht := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let : ∀ j, Finite (F j) := finite_endpoints ht
  have hab : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hgeom := source_critical_geometry ht d hc hab hd hb hcomm
  cases i
  · by_cases htriv : ⁅V F (base F true) 1 ⊓ Q F w,V F w 1⁆ = ⊥
    · obtain ⟨_,K,_,_,_,E,_,_,_,_,hE,_,⟨f⟩⟩ :=
        CommutingTrivial.reduced_critical_fields_two_from_chapterEight
          h models hc hab hd hb hcomm htriv
      obtain ⟨ea⟩ := Assembly.a5_graph_quotient h false a (base F false) rfl
      have heq := Nat.card_congr (ea.symm.trans f).toEquiv
      rw [nat_card_alternatingGroup,BenderSuzuki.External.huppert614_card_specialLinearGroup,hE]
        at heq
      norm_num [Nat.factorial] at heq
    · obtain ⟨z,hm,_⟩ := exists_moving_neighbor F
        (fun t => (source_Z_Q_U ht t).1) (base F true) w htriv
      have hw : (base F false).type ≠ w.type :=
        (odd_dist_iff F ht.generate (base F false) w).mp (hc.1.symm ▸ hgeom.1)
      have hztype : z.val.type = false := by
        have hzw := z.property.1
        change false ≠ w.type at hw
        cases hz : z.val.type <;> cases hwt : w.type <;> simp_all
      have hcentral := reduced_linear_moving_commutator_central h models hc hab hd hb hcomm
        z hm (a5_linear_marking h a z.val hztype).some
      obtain ⟨_,_,_,_,hAD,hDI,hIN,_⟩ :=
        reduced_critical_central_equivalences h models hc hab hd hb hcomm htriv
      have hnat := hIN.mp (hDI.mp (hAD.mp hcentral))
      exact natural_neighbor_central_involution_eq_one ht (reduced_borel_core_sylow h) d
        hab hgeom.2.2.1 hnat (models _) (a5_linear_marking h a _ rfl).some
        field_four_card x hx hx2
  · exact center_involution_eq_one_of_actor_center
      (local_center_eq_bot_of_neighbor_central ht d hab hgeom.2.2.1) x hx hx2

/-- Every full right central involution is trivial in a longer commuting
critical branch of the original pair with a left A5 quotient. -/
theorem original_a5_commuting_long_right_central_involution_eq_one
    (h : HypothesisF11 J S)
    (a : (J 0 ⧸ pCore 2 (J 0)) ≃* alternatingGroup (Fin 5))
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic J S i))
    {v w : Vertex F} (hc : IsCriticalPair F v w)
    (hb : 1 < b F) (hcomm : ⁅Z F v,Z F w⁆ = ⊥)
    (x : G₀ J S) (hx : x ∈ (center (stabilizer F (base F true))).map
      (stabilizer F (base F true)).subtype) (hx2 : x^2=1) : x=1 := by
  let ht := reduced_triple h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hwv : w ≠ v := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self] at hh
    omega
  obtain ⟨m,hvm,hd⟩ := exists_predecessor F ht.generate w v hwv
  rw [SimpleGraph.dist_comm (u := w) (v := m),
    SimpleGraph.dist_comm (u := w) (v := v),hc.1] at hd
  obtain ⟨g,hv,hm⟩ := incident_common_translate F hvm.2
  have htype : m.type = !v.type := Bool.eq_not_of_ne hvm.1.symm
  rw [htype] at hm
  have hv₀ : g⁻¹ • v = base F v.type := by
    simpa only [inv_smul_smul] using congrArg (fun z : Vertex F => g⁻¹ • z) hv.symm
  have hm₀ : g⁻¹ • m = base F (!v.type) := by
    simpa only [inv_smul_smul] using congrArg (fun z : Vertex F => g⁻¹ • z) hm.symm
  have hc₀ := criticalPair_translate F hc g⁻¹
  rw [hv₀] at hc₀
  have hcomm₀ : ⁅Z F (base F v.type),Z F (g⁻¹ • w)⁆ = ⊥ := by
    rw [←hv₀,commuting_centers_translate,hcomm,Subgroup.map_bot]
  have hd₀ : (graph F).dist (base F (!v.type)) (g⁻¹ • w) + 1 = b F := by
    rw [←hm₀,Subgroup.CosetGeometry.RankTwo.dist_smul]
    exact hd
  exact based_long_center h a (reduced_actor_models_of_nonsolvable_parabolics h hns)
    v.type hc₀ hd₀ hb hcomm₀ x hx hx2

end CFSG.Quasithin.ChapterF.Source
