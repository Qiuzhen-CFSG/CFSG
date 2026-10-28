module

public import Stellmacher.SectionNine.NineTenNormalizedExtraction
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionNine.NineThreeCenterSplitting
public import Stellmacher.SectionNine.NineEightNeighborhood
public import Stellmacher.SectionNine.NineSevenNeighborJoinBounds

/-!
# Excluding the predecessor core branch in (9.10)

Assume the predecessor module does not commute with the penultimate
center, and the initial center does not commute with a retained terminal
neighbor center. At critical length at least five, the penultimate center
cannot lie in the predecessor core.

Under that containment the nontrivial module commutator equals the
order-two predecessor center, by the exact next-orbit core action.
Distance bounds put the predecessor module in the preterminal stabilizer;
its commutator with the penultimate center therefore lies in preterminal V.
The abelian neighborhood join at the penultimate vertex makes this center
centralize terminal V. The first-step center already centralizes terminal V.
Their center splitting then makes the initial center centralize the retained
terminal neighbor center, a contradiction.

This is the core-containment exclusion immediately before Stellmacher
(9.10)(5), printed p.57 of `refs/files/stellmacher-n-group.pdf`. The earlier
assertion that the predecessor module and penultimate center do not commute
remains an explicit input here; it is not inferred from a pending result.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_predecessor_core_exclusion
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (predecessor neighbor : ctx.Γ.Vertex)
    (hpredecessor : ctx.Γ.adjacent ctx.criticalPath.a predecessor)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcenters : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥)
    (hmodules : ⁅VAt ctx.Γ predecessor,
      ZAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)⁆ ≠ ⊥) :
    ¬ ZAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤
      QAt ctx.Γ predecessor := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preceding := cp.path ⟨cp.length-3,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hshort : 1 < cp.length := by change 4 < cp.length at hb; omega
  have hpreMem : predecessor ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr hpredecessor
  obtain ⟨mover, hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hpreMem
  have horbit : IsConjugateVertex Γ cp.firstStep predecessor := ⟨mover, hmove⟩
  have hdata := nine_next_center_commutator_and_kernel ctx hshort predecessor horbit
  have hpreW : VAt Γ predecessor ≤ GeneratedNeighborhoodV Γ cp.a :=
    nine_eight_v_le_generated_neighborhood Γ hpreMem
  have hnear : Γ.distance cp.a preceding + 2 < cp.length := by
    have h := path_distance_le Γ cp 0 (cp.length-3) (Nat.zero_le _) (Nat.sub_le _ _)
    change Γ.distance (cp.path 0) preceding ≤ cp.length-3-0 at h
    rw [cp.path_start, Nat.sub_zero] at h
    change 4 < cp.length at hb
    omega
  have hWcore := nine_seven_neighborhood_le_core_of_distance Γ cp cp.a preceding hnear
  have hprecedingAdj : Γ.adjacent preceding preterminal := by
    have h := cp.path_adj ⟨cp.length-3,by change 4 < cp.length at hb; omega⟩
    convert h using 1 <;> apply congrArg cp.path <;> apply Fin.ext <;> simp
    change 4 < cp.length at hb
    omega
  have hcorePre : QAt Γ preceding ≤ GAt Γ preterminal :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core preceding preterminal
      ((mem_neighborhood_iff_adjacent Γ).mpr hprecedingAdj) default).2.2
  have hVpreG : VAt Γ predecessor ≤ GAt Γ preterminal := hpreW.trans (hWcore.trans hcorePre)
  have hpreterminalAdj : Γ.adjacent preterminal penultimate := by
    have h := cp.path_adj ⟨cp.length-2,by change 4 < cp.length at hb; omega⟩
    convert h using 1 <;> apply congrArg cp.path <;> apply Fin.ext <;> simp
    change 4 < cp.length at hb
    omega
  have hpenMem : penultimate ∈ neighborhood Γ cp.a' :=
    (nine_three_initial_extraction_inputs ctx.toLocalContext hshort).1
  have hpenAdj : Γ.adjacent penultimate cp.a' :=
    Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hpenMem)
  have hZpenV : ZAt Γ penultimate ≤ VAt Γ preterminal := by
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨penultimate, (mem_neighborhood_iff_adjacent Γ).mpr hpreterminalAdj, rfl⟩
  intro hcontain
  have hcommCenter : ⁅VAt Γ predecessor, ZAt Γ penultimate⁆ ≤ ZAt Γ predecessor :=
    (Subgroup.commutator_mono le_rfl hcontain).trans hdata.2.1.le
  have heq : ⁅VAt Γ predecessor, ZAt Γ penultimate⁆ = ZAt Γ predecessor := by
    apply Subgroup.eq_of_le_of_card_ge hcommCenter
    rw [hdata.1]
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hmodules
  have hcommV : ⁅VAt Γ predecessor, ZAt Γ penultimate⁆ ≤ VAt Γ preterminal :=
    (Subgroup.commutator_mono le_rfl hZpenV).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hVpreG.trans (stabilizer_le_normalizer_v Γ preterminal)))
  have hZpreV : ZAt Γ predecessor ≤ VAt Γ preterminal := heq ▸ hcommV
  have hpreterminalW : VAt Γ preterminal ≤ GeneratedNeighborhoodV Γ penultimate :=
    nine_eight_v_le_generated_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hpreterminalAdj))
  have hterminalW : VAt Γ cp.a' ≤ GeneratedNeighborhoodV Γ penultimate :=
    nine_eight_v_le_generated_neighborhood Γ ((mem_neighborhood_iff_adjacent Γ).mpr hpenAdj)
  have hWabel := nine_eight_neighborhood_abelian ctx.toLocalContext hb penultimate
  have hWcentral := Subgroup.le_centralizer_iff_isMulCommutative.mpr hWabel
  have hpreCentral : ZAt Γ predecessor ≤ Subgroup.centralizer (VAt Γ cp.a' : Set G) :=
    hZpreV.trans (hpreterminalW.trans (hWcentral.trans (Subgroup.centralizer_le hterminalW)))
  have hfirstCentral : ZAt Γ cp.firstStep ≤ Subgroup.centralizer (VAt Γ cp.a' : Set G) := by
    change z Γ cp.firstStep ≤ _
    rw [(lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center.2]
    exact (omegaOneCenter_le_centerAmbient _).trans
      ((centerAmbient_le_centralizer _).trans
        (Subgroup.centralizer_le (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2))
  have hdistinct : predecessor ≠ cp.firstStep := by
    intro heq
    apply hmodules
    rw [heq]
    have hVcore := (nine_three_initial_extraction_inputs ctx.toLocalContext hshort).2.1
    have hZcore := ((lemma_seven_three ctx.sectionSeven Γ).center_core penultimate cp.a'
      ((mem_neighborhood_iff_adjacent Γ).mpr hpenAdj)).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hZcore.trans (Subgroup.centralizer_le hVcore))
  have hsplit := nine_three_center_split ctx hshort ⟨1,Γ.act_one _⟩
    hpredecessor cp.firstStep_adj hdistinct
  have hinitialCentral : ZAt Γ cp.a ≤ Subgroup.centralizer (VAt Γ cp.a' : Set G) := by
    rw [hsplit.1]
    exact sup_le hpreCentral hfirstCentral
  have hneighborV : ZAt Γ neighbor ≤ VAt Γ cp.a' := by
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor,hneighbor,rfl⟩
  exact hcenters (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hinitialCentral.trans (Subgroup.centralizer_le hneighborV)))

end Stellmacher.SectionNine
