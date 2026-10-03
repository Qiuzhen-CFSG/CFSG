module

public import Stellmacher.SectionNine.NineTenPrescribedActorGeometry
public import Stellmacher.SectionNine.NineTenPrescribedFirstTransvection
public import Stellmacher.SectionNine.NineTenCommonNeighborGeneration
public import Stellmacher.SectionNine.NineTenExtractedPredecessor
public import Stellmacher.SectionNine.LemmaNineFour

/-!
# The reversed commutator lies in the first and predecessor modules

For the actual normalized extraction, the commutator of predecessor V with
the penultimate center lies in the intersection of predecessor V and the
original first module. Both geometric extraction packets and the original
prescribed actor are retained. No additional critical pair is assumed.

Critical minimality puts the penultimate center in the initial core and
hence in the predecessor stabilizer, giving containment in predecessor V.
The initial neighborhood lies in the preterminal stabilizer, so the same
commutator lies in preterminal V. Both preterminal and terminal V lie in the
abelian penultimate neighborhood. The prescribed actor in a terminal-neighbor
center therefore centralizes the commutator. Apply the genuine (9.4) with
the original residual conjugator, its already proved geometry and universal
common-neighbor generation, and the first extraction's coatom transvection.

This proves the first assertion on printed p.58 of Stellmacher (9.10):
R0=[V_{a-1},Z_{a'-1}] lies in V_{a+1} intersect V_{a-1}. The next choice of
orientation and its transvection input remain separate proof obligations.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_reversed_commutator_containment
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second)
    (hactorNeighbor : actor ∈ ZAt ctx.Γ neighbor)
    (hactorComm : twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆)
    (hnew : ctx.Γ.act data.x⁻¹ second = ctx.criticalPath.a)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (firstActor : G) (firstE firstA0 : Subgroup G)
    (firstData : NineThreeGeometricData ctx.Γ ctx.criticalPath.a'
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
      (VAt ctx.Γ ctx.criticalPath.firstStep) firstE firstA0 firstActor)
    (hfirstNew : ctx.Γ.act firstData.x⁻¹
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) =
        neighbor) :
    ⁅VAt ctx.Γ (ctx.Γ.act data.x⁻¹ (ctx.criticalPath.path ⟨3, by omega⟩)),
      ZAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        VAt ctx.Γ (ctx.Γ.act data.x⁻¹ (ctx.criticalPath.path ⟨3, by omega⟩)) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 4 < cp.length := hb
  have hshort : 1 < cp.length := by omega
  let third := cp.path ⟨3, by omega⟩
  let predecessor := Γ.act data.x⁻¹ third
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let R0 := ⁅VAt Γ predecessor, ZAt Γ penultimate⁆
  have hthird : IsCriticalPathOffset Γ cp 3 third := ⟨⟨3, by omega⟩, rfl, rfl⟩
  have hpred := (nine_ten_extracted_predecessor_alternative Γ cp (by omega)
    second actor E A0 data hsecond hnew).1
  have hpenQa : ZAt Γ penultimate ≤ QAt Γ cp.a := by
    have hdist := path_distance_le Γ cp 0 (cp.length - 1) (Nat.zero_le _) (Nat.sub_le _ _)
    change Γ.distance (cp.path 0) penultimate ≤ cp.length - 1 - 0 at hdist
    rw [cp.path_start, Nat.sub_zero] at hdist
    apply critical_minimality Γ cp
    rw [Γ.distance_symm]
    omega
  have hQaPred : QAt Γ cp.a ≤ GAt Γ predecessor :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a predecessor
      ((mem_neighborhood_iff_adjacent Γ).mpr hpred) default).2.2
  have hRpred : R0 ≤ VAt Γ predecessor :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((hpenQa.trans hQaPred).trans (stabilizer_le_normalizer_v Γ predecessor))
  have hpredW : VAt Γ predecessor ≤ GeneratedNeighborhoodV Γ cp.a :=
    nine_eight_v_le_generated_neighborhood Γ ((mem_neighborhood_iff_adjacent Γ).mpr hpred)
  have hWpre : GeneratedNeighborhoodV Γ cp.a ≤ GAt Γ preterminal :=
    nine_eight_neighborhood_le_preterminal ctx.toLocalContext hb cp.a
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
  have hpreAdj : Γ.adjacent preterminal penultimate := by
    have h := cp.path_adj ⟨cp.length - 2, by omega⟩
    have hindex : (⟨cp.length - 2, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    simpa only [hindex, Fin.castSucc_mk, preterminal, penultimate] using h
  have hpenV : ZAt Γ penultimate ≤ VAt Γ preterminal := by
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨penultimate, (mem_neighborhood_iff_adjacent Γ).mpr hpreAdj, rfl⟩
  have hRpre : R0 ≤ VAt Γ preterminal :=
    (Subgroup.commutator_mono le_rfl hpenV).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        ((hpredW.trans hWpre).trans (stabilizer_le_normalizer_v Γ preterminal)))
  have hpenMem : penultimate ∈ neighborhood Γ cp.a' :=
    (nine_three_initial_extraction_inputs ctx.toLocalContext hshort).1
  have hpreW : VAt Γ preterminal ≤ GeneratedNeighborhoodV Γ penultimate :=
    nine_eight_v_le_generated_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hpreAdj))
  have hterminalW : VAt Γ cp.a' ≤ GeneratedNeighborhoodV Γ penultimate :=
    nine_eight_v_le_generated_neighborhood Γ ((mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hpenMem)))
  have hactorV : actor ∈ VAt Γ cp.a' := by
    apply (show ZAt Γ neighbor ≤ VAt Γ cp.a' from ?_) hactorNeighbor
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hactorW : Subgroup.zpowers actor ≤ GeneratedNeighborhoodV Γ penultimate :=
    Subgroup.zpowers_le.mpr (hterminalW hactorV)
  have hcentral := Subgroup.le_centralizer_iff_isMulCommutative.mpr
    (nine_eight_neighborhood_abelian ctx.toLocalContext hb penultimate)
  have hRcentral : R0 ≤ Subgroup.centralizer (Subgroup.zpowers actor : Set G) :=
    (hRpre.trans hpreW).trans (hcentral.trans (Subgroup.centralizer_le hactorW))
  have hcomm : ⁅R0, Subgroup.zpowers actor⁆ ≤ VAt Γ cp.firstStep := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRcentral]
    exact bot_le
  obtain ⟨hdistance, hactorGeometry, hactorNotCore, hxComm, _⟩ :=
    nine_ten_prescribed_actor_geometry ctx.toLocalContext third second neighbor
      hthird hneighbor actor E A0 data hactorNeighbor hactorComm
  have hindex : QuotientCardEq (VAt Γ cp.firstStep)
      (VAt Γ cp.firstStep ⊓ GAt Γ neighbor) 2 := by
    change Nat.card (VAt Γ cp.firstStep) =
      2 * Nat.card (VAt Γ cp.firstStep ⊓ GAt Γ neighbor : Subgroup G)
    rw [← hfirstNew, ← firstData.coatom_eq]
    exact firstData.coatom_card
  have hdisplacement := (nine_ten_prescribed_actor_first_transvection ctx hshort hterminalNot
    neighbor hneighbor hindex actor hactorNeighbor hactorNotCore).2
  have hgeneration : ∀ n : Γ.Vertex,
      n ∈ Neighborhood Γ cp.firstStep → n ∈ Neighborhood Γ predecessor →
      (GAt Γ cp.firstStep ⊓ GAt Γ n) ⊔ Subgroup.zpowers actor = GAt Γ cp.firstStep :=
    nine_ten_prescribed_actor_common_neighbor_generation ctx.toLocalContext third second neighbor
      hthird hneighbor actor E A0 data hactorNeighbor
  exact le_inf (lemma_nine_four_ambient ctx hshort third hdistance actor hactorGeometry
    data.x⁻¹ hxComm R0 hRpred hcomm hgeneration hdisplacement) hRpred

end Stellmacher.SectionNine
