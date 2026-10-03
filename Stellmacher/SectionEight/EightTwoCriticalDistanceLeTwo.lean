module
public import Stellmacher.SectionEight.EightTwoTwoBackwardShifts
public import Stellmacher.SectionEight.EightTwoShiftedCommutatorCentral

/-!
# Critical length at most two in the noncentral case

For the exact local context of Stellmacher (8.2), noncentrality of the
first-step vertex center forces critical distance at most two. No structural
or normality hypothesis is imposed beyond that original local context.

If the critical path has length greater than two, choose the two actual
backward neighbors and their critical pairs. The second pair's commutator
R2 lies in both endpoint centers and is central in the first backward
stabilizer by the shifted-commutator theorem. Its opposite endpoint is two
steps from the original terminal vertex, so critical minimality makes R2
commute with the original terminal center. The first generating equality
therefore makes R2 central in the initial stabilizer as well. These adjacent
stabilizers generate the ambient group. Their common central subgroup is a
two-group by characteristic two, hence trivial because the ambient two-core
vanishes. This contradicts noncommutation of the second critical pair.

Source: Stellmacher (8.2), Journal of Algebra 190 (1997), printed pp.37–38,
refs/latex/stellmacher-n-group.tex, the contradiction under b>2. The separate
b=2 argument and the final distance-one assembly are not assumed here.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem backward_antepenultimate_distance
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (hlen : 1 < cp.length) (m : Γ.Vertex) (hm : m ∈ neighborhood Γ cp.a) :
    Γ.distance (cp.path ⟨cp.length - 2, by omega⟩) m < cp.length := by
  let route : Fin (cp.length - 1 + 1) → Γ.Vertex := fun i =>
    if i.val = 0 then m else cp.path ⟨i.val - 1, by omega⟩
  have hzero : route 0 = m := by simp [route]
  have hfinal : route ⟨cp.length - 1, Nat.lt_succ_self _⟩ =
      cp.path ⟨cp.length - 2, by omega⟩ := by
    simp only [route, show cp.length - 1 ≠ 0 by omega, ↓reduceIte,
      Nat.sub_sub, Nat.reduceAdd]
  have hadj : ∀ i : Fin (cp.length - 1),
      Γ.adjacent (route i.castSucc) (route i.succ) := by
    intro i
    simp only [route, Fin.val_castSucc, Fin.val_succ]
    by_cases hzero : i.val = 0
    · simpa [hzero, cp.path_start] using
        Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hm)
    · have hstep := cp.path_adj ⟨i.val - 1, by omega⟩
      simpa [hzero, Nat.sub_add_cancel (by omega : 1 ≤ i.val)] using hstep
  have hd := Γ.distance_le_of_path (cp.length - 1) route hadj
  rw [hzero, hfinal] at hd
  rw [Γ.distance_symm]
  exact hd.trans_lt (by omega)

private theorem second_commutator_central_at_initial
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlen : 2 < ctx.criticalPath.length) (m n : ctx.Γ.Vertex)
    (hgen : (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m) ⊔
      ZAt ctx.Γ ctx.criticalPath.a' = GAt ctx.Γ ctx.criticalPath.a)
    (hcrit : IsCriticalPair ctx.Γ n
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2, by omega⟩))
    (hcentral : ⁅ZAt ctx.Γ n,
      ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2, by omega⟩)⁆ ≤
        CenterAmbient (GAt ctx.Γ m)) :
    ⁅ZAt ctx.Γ n,
      ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2, by omega⟩)⁆ ≤
        CenterAmbient (GAt ctx.Γ ctx.criticalPath.a) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  change 2 < cp.length at hlen
  let right := cp.path ⟨cp.length - 2, by omega⟩
  let last := cp.path ⟨cp.length - 1, by omega⟩
  let R := ⁅z Γ n, z Γ right⁆
  have hRright : R ≤ z Γ right :=
    (critical_pair_commutator_le_inf ctx.sectionSeven Γ cp n right hcrit).trans inf_le_right
  have hdistStart : Γ.distance right cp.a < cp.length := by
    have hd := SevenSix.path_distance_le Γ cp 0 (cp.length - 2) (by omega) (by omega)
    rw [Fin.mk_zero, cp.path_start, Nat.sub_zero] at hd
    rw [Γ.distance_symm]
    exact hd.trans_lt (by omega)
  have hdistEnd : Γ.distance right cp.a' < cp.length := by
    have hd := SevenSix.path_distance_le Γ cp (cp.length - 2) cp.length (by omega) le_rfl
    rw [cp.path_end] at hd
    exact hd.trans_lt (by omega)
  have hRinitial : R ≤ stabilizer Γ cp.a :=
    hRright.trans ((SevenSix.critical_minimality Γ cp hdistStart).trans
      (by rw [q, Γ.twoCoreAt_def]; exact Subgroup.map_subtype_le _))
  have hRterminalCore : R ≤ q Γ cp.a' :=
    hRright.trans (SevenSix.critical_minimality Γ cp hdistEnd)
  have hlast : last ∈ neighborhood Γ cp.a' := by
    apply (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    have ha := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hi : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by apply Fin.ext; dsimp; omega
    rw [hi, cp.path_end] at ha
    exact Γ.adjacent_symm ha
  have hZterminal : z Γ cp.a' ≤ Subgroup.centralizer (q Γ cp.a' : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a' last hlast).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        (SevenSix.centerAmbient_le_centralizer _))
  have hnextC : z Γ cp.a' ≤ Subgroup.centralizer (R : Set G) :=
    hZterminal.trans (Subgroup.centralizer_le hRterminalCore)
  have hmiddleC : stabilizer Γ m ≤ Subgroup.centralizer (R : Set G) :=
    Subgroup.le_centralizer_iff.mp
      (hcentral.trans (SevenSix.centerAmbient_le_centralizer _))
  have hstartC : stabilizer Γ cp.a ≤ Subgroup.centralizer (R : Set G) := by
    change (stabilizer Γ cp.a ⊓ stabilizer Γ m) ⊔ z Γ cp.a' = stabilizer Γ cp.a at hgen
    rw [← hgen]
    exact sup_le (inf_le_right.trans hmiddleC) hnextC
  intro element helement
  refine ⟨⟨element, hRinitial helement⟩, ?_, rfl⟩
  change (⟨element, hRinitial helement⟩ : stabilizer Γ cp.a) ∈
    Subgroup.center (stabilizer Γ cp.a)
  rw [Subgroup.mem_center_iff]
  intro other
  exact Subtype.ext
    (Subgroup.mem_centralizer_iff.mp (hstartC other.property) element helement).symm

private theorem common_central_subgroup_eq_bot
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (m : ctx.Γ.Vertex) (hm : m ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (R : Subgroup G)
    (hleft : R ≤ CenterAmbient (GAt ctx.Γ ctx.criticalPath.a))
    (hright : R ≤ CenterAmbient (GAt ctx.Γ m)) : R = ⊥ := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  have hPC : P ≤ Subgroup.centralizer (R : Set G) :=
    Subgroup.le_centralizer_iff.mp (hleft.trans (SevenSix.centerAmbient_le_centralizer _))
  have hMC : stabilizer Γ m ≤ Subgroup.centralizer (R : Set G) :=
    Subgroup.le_centralizer_iff.mp (hright.trans (SevenSix.centerAmbient_le_centralizer _))
  obtain ⟨_, _, _, _, hgen, _⟩ := edge_sectionThree_data ctx.sectionSeven Γ hm
    (default : Sylow 2 ↥(stabilizer Γ cp.a ⊓ stabilizer Γ m))
  have htopC : (⊤ : Subgroup G) ≤ Subgroup.centralizer (R : Set G) := by
    rw [← hgen]
    exact sup_le hPC hMC
  have hRN : R.Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_unique (htopC.trans (Subgroup.centralizer_le_normalizer (R : Set G))))
  have hcenterCore : Subgroup.center P ≤ pCore 2 P :=
    (Subgroup.center_le_centralizer _).trans
      (SevenSix.edge_characteristic_data ctx.sectionSeven Γ cp).1
  have hRp : IsPGroup 2 R :=
    ((pCore_isPGroup (p := 2) (G := P)).map P.subtype).to_le
      (hleft.trans (Subgroup.map_mono hcenterCore))
  exact le_bot_iff.mp
    ((show R ≤ pCore 2 G from le_sSup ⟨hRN, hRp⟩).trans_eq ctx.sectionSeven.twoCore_eq_bot)

public theorem eight_two_critical_distance_le_two_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ctx.criticalPath.length ≤ 2 := by
  by_contra hlarge
  have hlen : 2 < ctx.criticalPath.length := by omega
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  change 2 < cp.length at hlen
  obtain ⟨m, n, hm, hn, hgen1, hgen2, _hcrit1, hcrit2, _hout1, _hout2⟩ :=
    eight_two_exists_two_backward_shifts_local ctx hcenter (by omega)
  let right := cp.path ⟨cp.length - 2, by omega⟩
  let last := cp.path ⟨cp.length - 1, by omega⟩
  have hdistMiddle : Γ.distance right m < cp.length :=
    backward_antepenultimate_distance Γ cp (by omega) m hm
  have hdistNext : Γ.distance last right < cp.length := by
    have hd := SevenSix.path_distance_le Γ cp (cp.length - 2) (cp.length - 1)
      (by omega) (by omega)
    rw [Γ.distance_symm]
    exact hd.trans_lt (by omega)
  have hcentralMiddle := eight_two_shifted_commutator_central_local
    ctx hcenter n m right last hn hcrit2 hdistMiddle hdistNext hgen2
  have hcentralInitial := second_commutator_central_at_initial
    ctx hlen m n hgen1 hcrit2 hcentralMiddle
  have hbot := common_central_subgroup_eq_bot ctx m hm _ hcentralInitial hcentralMiddle
  exact eight_two_critical_pair_commutator_ne_local ctx hcenter n right hcrit2 hbot

end Stellmacher.SectionEight
