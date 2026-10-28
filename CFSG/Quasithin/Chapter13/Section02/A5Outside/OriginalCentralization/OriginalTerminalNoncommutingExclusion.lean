module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalTerminalReducedCenter
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalBOneExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.OriginalA5BTwoMiddleCenter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicNoncommutingBound

/-!
# Every terminal critical pair has commuting centers

The original terminal central line survives in the full reduced right
stabilizer. Distance one is excluded by the original chosen left module.
At distance two, a right critical endpoint has trivial intrinsic center;
when the right endpoint is the middle vertex, the original left A5 quotient
supplies the fixed-point-free cubic action on the same line.

This excludes the entire noncommuting branch without a right quotient
marking or native comparison. The commuting branch is retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric ChapterF.Source
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H R : Subgroup G}

private theorem center_involution_eq_one_of_actor_center
    {X : Type*} [Group X] {P : Subgroup X}
    (hc : center (Theory.GroupTheory.AmalgamGraph.sylowGenerated P) = ⊥)
    (x : X) (hx : x ∈ (center P).map P.subtype) (hx2 : x^2=1) : x=1 := by
  obtain ⟨z,hz,rfl⟩ := hx
  have hp : IsPGroup 2 (zpowers (z : X)) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hx2).isPGroup 2 _
  have hza : (z : X) ∈ Theory.GroupTheory.AmalgamGraph.sylowGenerated P :=
    Theory.GroupTheory.AmalgamGraph.pGroup_le_sylowGenerated P _
      (zpowers_le.mpr z.property) hp (mem_zpowers _)
  have hzc : (⟨z,hza⟩ : Theory.GroupTheory.AmalgamGraph.sylowGenerated P) ∈
      center (Theory.GroupTheory.AmalgamGraph.sylowGenerated P) := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    change (y : X) * (z : X) = (z : X) * (y : X)
    exact congrArg P.subtype (mem_center_iff.mp hz
      ⟨y,Theory.GroupTheory.AmalgamGraph.sylowGenerated_le P y.property⟩)
  have he : (⟨z,hza⟩ : Theory.GroupTheory.AmalgamGraph.sylowGenerated P) = 1 := by
    apply mem_bot.mp
    rwa [hc] at hzc
  exact congrArg (Theory.GroupTheory.AmalgamGraph.sylowGenerated P).subtype he

private theorem terminal_graph_central_involution
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer (V₁ : Set G)) (hR : R ≤ H)
    (h : HypothesisF11 ![L,R] (Global.sourceS L H)) :
    ∃ x : G₀ ![L,R] (Global.sourceS L H), x ≠ 1 ∧ x^2=1 ∧
      x ∈ (center (stabilizer (reducedFamily ![L,R] (Global.sourceS L H))
        (base (reducedFamily ![L,R] (Global.sourceS L H)) true))).map
        (stabilizer (reducedFamily ![L,R] (Global.sourceS L H))
          (base (reducedFamily ![L,R] (Global.sourceS L H)) true)).subtype := by
  let S := Global.sourceS L H
  let P := P₀ ![L,R] S 1
  have hzP : V₁ ≤ (center P).map P.subtype := by
    rw [show P = parabolic ![L,R] (SuzukiContainment.reducedSylow ![L,R] S) 1 from P₀_eq_source h 1]
    exact (original_terminal_reduced_right_center d hH hHC hR h).1
  have hv : V₁ ≠ ⊥ := by
    intro he
    have hc := d.flag.one_card
    rw [he] at hc
    norm_num at hc
  obtain ⟨⟨z,hz⟩,hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hv
  have hz1 : z ≠ 1 := fun he => hz1' (Subtype.ext he)
  have hz2 : z^2=1 := by
    have hp := pow_card_eq_one' (x := (⟨z,hz⟩ : V₁))
    rw [d.flag.one_card] at hp
    exact congrArg Subtype.val hp
  obtain ⟨zp,hzp,hp⟩ := hzP hz
  let e := subgroupOfEquivOfLe (show P ≤ G₀ ![L,R] S from le_sup_right)
  let y := e.symm zp
  have hyc : y ∈ center (P.subgroupOf (G₀ ![L,R] S)) :=
    (centerCongr e.symm ⟨zp,hzp⟩).property
  have hyval : ((y : G₀ ![L,R] S) : G) = z := hp
  refine ⟨y,?_,?_,?_⟩
  · intro he
    exact hz1 (hyval.symm.trans (congrArg Subtype.val he))
  · apply Subtype.ext
    change (((y : G₀ ![L,R] S) : G)^2) = 1
    rw [hyval]
    exact hz2
  · have he : stabilizer (reducedFamily ![L,R] S)
        (base (reducedFamily ![L,R] S) true) = P.subgroupOf (G₀ ![L,R] S) :=
      Subgroup.CosetGeometry.stabilizer_base _ _
    change (y : G₀ ![L,R] S) ∈ (center (stabilizer (reducedFamily ![L,R] S)
      (base (reducedFamily ![L,R] S) true))).map _
    rw [he]
    exact mem_map_of_mem (P.subgroupOf (G₀ ![L,R] S)).subtype hyc

/-- Every actual critical pair in the terminal original F.1.1 pair has
commuting centers. The right factor need only lie in the original H. -/
theorem original_terminal_critical_centers_commute
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer (V₁ : Set G)) (hR : R ≤ H)
    (h : HypothesisF11 ![L,R] (Global.sourceS L H))
    {v w : Vertex (reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (reducedFamily ![L,R] (Global.sourceS L H)) v w) :
    ⁅Z (reducedFamily ![L,R] (Global.sourceS L H)) v,
      Z (reducedFamily ![L,R] (Global.sourceS L H)) w⁆ = ⊥ := by
  by_contra hne
  let S := Global.sourceS L H
  let F := reducedFamily ![L,R] S
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  rcases reduced_intrinsic_noncommuting_bound h hc hne with hb | hb
  · exact original_context_critical_bOne_impossible d h hc hne hb
  change b F = 2 at hb
  have hwv : w ≠ v := by
    intro he
    have hd := hc.1
    rw [he,SimpleGraph.dist_self] at hd
    change 0 = b F at hd
    change b F = 2 at hb
    omega
  obtain ⟨m,hvm,hd⟩ := exists_predecessor F (reduced_triple h).generate w v hwv
  rw [SimpleGraph.dist_comm (u := w) (v := m),
    SimpleGraph.dist_comm (u := w) (v := v),hc.1] at hd
  obtain ⟨g,hv,hm⟩ := incident_common_translate F hvm.2
  have htype : m.type = !v.type := Bool.eq_not_of_ne hvm.1.symm
  rw [htype] at hm
  have hv₀ : g⁻¹ • v = base F v.type := by
    simpa only [inv_smul_smul] using congrArg (fun z : Vertex F => g⁻¹ • z) hv.symm
  have hm₀ : g⁻¹ • m = base F (!v.type) := by
    simpa only [inv_smul_smul] using congrArg (fun z : Vertex F => g⁻¹ • z) hm.symm
  have hc₀ := CommutingNontrivial.criticalPair_translate F hc g⁻¹
  rw [hv₀] at hc₀
  have hne₀ : ⁅Z F (base F v.type),Z F (g⁻¹ • w)⁆ ≠ ⊥ := by
    rw [←hv₀,CommutingNontrivial.commuting_centers_translate]
    intro he
    exact hne ((Subgroup.map_eq_bot_iff_of_injective
      (⁅Z F v,Z F w⁆) (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective).mp he)
  have hd₀ : (graph F).dist (base F (!v.type)) (g⁻¹ • w) + 1 = b F := by
    rw [←hm₀,Subgroup.CosetGeometry.RankTwo.dist_smul]
    exact hd
  have hmw : (graph F).Adj (base F (!v.type)) (g⁻¹ • w) :=
    SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  obtain ⟨x,hx1,hx2,hxc⟩ := terminal_graph_central_involution d hH hHC hR h
  cases hvtype : v.type
  · rw [hvtype] at hc₀ hne₀ hmw
    exact hx1 (original_a5_bTwo_middle_central_involution_eq_one h d.quotient
      hc₀ hne₀ hb hmw x hxc hx2)
  · rw [hvtype] at hc₀ hne₀ hmw
    have hbase : (graph F).Adj (base F true) (base F false) :=
      ⟨by change true ≠ false; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
    have hz := (reduced_bTwo_center_identities h hc₀ hne₀ hb hbase hmw).2.1
    exact hx1 (center_involution_eq_one_of_actor_center hz x hxc hx2)

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
