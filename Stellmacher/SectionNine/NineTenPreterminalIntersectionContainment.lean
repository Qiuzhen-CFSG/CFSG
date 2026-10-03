module

public import Stellmacher.SectionNine.NineTenPrescribedActorGeometry
public import Stellmacher.SectionNine.NineTenPrescribedFirstTransvection
public import Stellmacher.SectionNine.NineTenCommonNeighborGeneration
public import Stellmacher.SectionNine.LemmaNineFour

/-!
# The predecessor/preterminal intersection lies in the first module

Retain the actual second extraction actor, its residual conjugator bound,
and the first extraction's coatom. At critical distance at least five, the
intersection of the extracted predecessor module with the preterminal module
lies in the first-step module.

Both preterminal V and terminal V lie in the abelian neighborhood generated
at the penultimate vertex. The prescribed actor belongs to terminal V and
therefore centralizes the entire intersection. Apply genuine (9.4) to this
intersection, using the same third vertex and inverse conjugator, the proved
common-neighbor generation, and the first coatom's transvection displacement.

This strengthens the commutator placement used just after Stellmacher
(9.10)(5), printed p.58. On the actual reversed critical path, (7.4) gives
mutual normalization of the predecessor and preterminal modules. Their full
commutator then lies in this intersection. Thus a genuine transvection from
(9.8) on that reversed path has its commutator in the required backward
module, without transferring a coatom from a different critical pair.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_preterminal_intersection_le_first
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hactorNeighbor : actor ∈ ZAt ctx.Γ neighbor)
    (hactorComm : twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (firstActor : G) (firstE firstA0 : Subgroup G)
    (firstData : NineThreeGeometricData ctx.Γ ctx.criticalPath.a'
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
      (VAt ctx.Γ ctx.criticalPath.firstStep) firstE firstA0 firstActor)
    (hfirstNew : ctx.Γ.act firstData.x⁻¹
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) =
        neighbor) :
    VAt ctx.Γ (ctx.Γ.act data.x⁻¹ (ctx.criticalPath.path ⟨3, by omega⟩)) ⊓
      VAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 4 < cp.length := hb
  have hshort : 1 < cp.length := by omega
  let third := cp.path ⟨3, by omega⟩
  let predecessor := Γ.act data.x⁻¹ third
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let I := VAt Γ predecessor ⊓ VAt Γ preterminal
  have hthird : IsCriticalPathOffset Γ cp 3 third := ⟨⟨3, by omega⟩, rfl, rfl⟩
  have hpreAdj : Γ.adjacent preterminal penultimate := by
    have h := cp.path_adj ⟨cp.length - 2, by omega⟩
    have hindex : (⟨cp.length - 2, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    simpa only [hindex, Fin.castSucc_mk, preterminal, penultimate] using h
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
  have hIcentral : I ≤ Subgroup.centralizer (Subgroup.zpowers actor : Set G) :=
    (inf_le_right.trans hpreW).trans (hcentral.trans (Subgroup.centralizer_le hactorW))
  have hcomm : ⁅I, Subgroup.zpowers actor⁆ ≤ VAt Γ cp.firstStep := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hIcentral]
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
  exact lemma_nine_four_ambient ctx hshort third hdistance actor hactorGeometry
    data.x⁻¹ hxComm I inf_le_left hcomm hgeneration hdisplacement

end Stellmacher.SectionNine
