module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalTerminalNoncommutingExclusion
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalCommutingOneExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.OriginalA5CommutingLongCenter

/-!
# No terminal original F.1.1 pair beside the chosen A5 module

The original terminal central line gives a nontrivial central involution in
its full reduced right parabolic. The genuine noncommuting exclusion forces
commuting centers. Distance one is excluded by the original faithful chosen
module; the longer commuting branch kills the same central involution.

The selected right factor is arbitrary, perfect and nontrivial. It need
only lie in the original terminal H. No right quotient marking, normalized
Borel, prepared pair or classification alternative is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric ChapterF.Source
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H R : Subgroup G}

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

private theorem original_parabolics_nonsolvable
    (d : Context T L V V₁ V₂ V₃) (S : Subgroup G)
    (hp : Group.IsPerfect R) (hne : R ≠ ⊥) :
    ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic ![L,R] S i) := by
  have hn : ∀ i : Fin 2, ¬ Group.IsSolvable (![L,R] i) := by
    intro i
    fin_cases i
    · exact Chapter1.mem_L_not_isSolvable
        ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
          d.hypothesis.local_component).1
    · let := hp
      let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hne
      exact Group.IsPerfect.not_isSolvable R
  intro i hs
  let := hs
  exact hn i (Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show ![L,R] i ≤ parabolic ![L,R] S i from
      le_sup_left.trans le_sup_left)) (inclusion_injective _))

/-- The longer commuting branch is impossible for the actual terminal
right factor and the original chosen A5 left module. -/
theorem original_terminal_commuting_long_impossible
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer (V₁ : Set G)) (hR : R ≤ H)
    (h : HypothesisF11 ![L,R] (Global.sourceS L H))
    (hp : Group.IsPerfect R) (hne : R ≠ ⊥)
    {v w : Vertex (reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (reducedFamily ![L,R] (Global.sourceS L H)) v w)
    (hb : 1 < b (reducedFamily ![L,R] (Global.sourceS L H)))
    (hcomm : ⁅Z (reducedFamily ![L,R] (Global.sourceS L H)) v,
      Z (reducedFamily ![L,R] (Global.sourceS L H)) w⁆ = ⊥) : False := by
  obtain ⟨x,hx1,hx2,hxc⟩ := terminal_graph_central_involution d hH hHC hR h
  exact hx1 (original_a5_commuting_long_right_central_involution_eq_one h d.quotient
    (original_parabolics_nonsolvable d _ hp hne) hc hb hcomm x hxc hx2)

/-- No actual terminal F.1.1 pair has the original chosen A5 left module
and a nontrivial perfect right factor inside H. -/
theorem original_terminal_pair_impossible
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer (V₁ : Set G)) (hR : R ≤ H)
    (h : HypothesisF11 ![L,R] (Global.sourceS L H))
    (hp : Group.IsPerfect R) (hne : R ≠ ⊥) : False := by
  let F := reducedFamily ![L,R] (Global.sourceS L H)
  obtain ⟨v,w,hc⟩ := reduced_criticalPair h
  have hcomm := original_terminal_critical_centers_commute d hH hHC hR h hc
  have hbpos : 0 < b F := source_b_positive (reduced_triple h)
  by_cases hb : b F = 1
  · have hbase : ⁅Z F (base F false),Z F (base F true)⁆ = ⊥ := by
      rcases CommutingOneProfile.original_critical_base_edge_or_reverse h hb with hc₀ | hc₀
      · exact original_terminal_critical_centers_commute d hH hHC hR h hc₀
      · rw [commutator_comm]
        exact original_terminal_critical_centers_commute d hH hHC hR h hc₀
    exact original_context_commuting_bOne_impossible d h hp hne hb hbase
  · exact original_terminal_commuting_long_impossible d hH hHC hR h hp hne hc
      (by change 1 < b F; omega) hcomm

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
