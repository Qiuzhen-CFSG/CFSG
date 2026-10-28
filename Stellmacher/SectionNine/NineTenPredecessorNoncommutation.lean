module
public import Stellmacher.SectionNine.NineTenPrescribedActorGeometry
public import Stellmacher.SectionNine.NineTenPrescribedFirstTransvection
public import Stellmacher.SectionNine.NineTenPredecessorDisplacementBound
public import Stellmacher.SectionNine.NineTenPredecessorLargeSubgroup
public import Stellmacher.SectionNine.NineTenPredecessorCoatomObstruction
public import Stellmacher.SectionNine.NineTenExtractedPredecessor
public import Stellmacher.SectionNine.LemmaNineFour
public import Stellmacher.SectionNine.NineTenCommonNeighborGeneration
public import Stellmacher.SectionNine.LemmaNineEight
public import Stellmacher.SectionNine.LemmaNineNine

/-!
# The extracted predecessor does not centralize the penultimate center

Retain both actual normalized geometric extraction packets. The module at
the extracted predecessor fails to centralize the penultimate center.
The actor and residual conjugator in the application of (9.4) are the
original second extraction witnesses throughout the proof.

If the two groups commute, the predecessor lies in the terminal stabilizer.
The selected canonical support makes its commutator with the retained
terminal-neighbor center lie in R joined with the terminal central line,
where R lies in the first module. The fixed-displacement kernel supplies
a subgroup of at least half the predecessor order whose commutator with
the same prescribed actor lies in that first module. The actual coatom
gives the actor's transvection displacement. Residual Sylow generation
proves every common-neighbor edge-generation hypothesis. The genuine
ambient (9.4) puts this subgroup in the first module, contradicting the
proved half-order obstruction from (9.7).

This proves the noncommutation immediately before Stellmacher (9.10)(5),
printed p.57. It neither identifies the generic extraction subgroup with
a smaller center-generated group nor chooses a new actor or critical path.
The normalized existential producer uses the actual (9.8) and (9.9) bounds
to obtain the two center noncontainments from b>3. It retains both original
extraction packets and states the noncommutation for their exact third
path offset, so subsequent reversed-pair constructions use these witnesses.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_predecessor_noncommutation
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second)
    (hactorNeighbor : actor ∈ ZAt ctx.Γ neighbor)
    (hactorComm : twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆)
    (hnew : ctx.Γ.act data.x⁻¹ second = ctx.criticalPath.a)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcenters : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥)
    (firstActor : G) (firstE firstA0 : Subgroup G)
    (firstData : NineThreeGeometricData ctx.Γ ctx.criticalPath.a'
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
      (VAt ctx.Γ ctx.criticalPath.firstStep) firstE firstA0 firstActor)
    (hfirstNew : ctx.Γ.act firstData.x⁻¹
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) =
        neighbor)
    (hfirstActors : ∀ b : G, b ∈ VAt ctx.Γ ctx.criticalPath.firstStep → b ∉ firstA0 →
      twoResidualIn firstE ≤ ⁅twoResidualIn firstE, Subgroup.zpowers b⁆) :
    ⁅VAt ctx.Γ (ctx.Γ.act data.x⁻¹ (ctx.criticalPath.path ⟨3, by omega⟩)),
      ZAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)⁆ ≠ ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 4 < cp.length := hb
  let third := cp.path ⟨3, by omega⟩
  let predecessor := Γ.act data.x⁻¹ third
  have hthird : IsCriticalPathOffset Γ cp 3 third := ⟨⟨3, by omega⟩, rfl, rfl⟩
  have hshort : 1 < cp.length := by omega
  obtain ⟨hdistance, hactorGeometry, hactorNotCore, hxComm, hxFirst⟩ :=
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
  obtain ⟨selected, hselected, _, hnotCore, hN, hW, action, hformula, hkernel, hyp,
    hfactor, hsupport⟩ := nine_ten_selected_factor_support
    ctx hshort hterminalNot hfirstNot neighbor second actor E A0 data hnew hneighbor hcenters
      firstActor firstE firstA0 firstData hfirstNew hfirstActors
  let _ := hN
  let _ := hW
  have hpred := (nine_ten_extracted_predecessor_alternative Γ cp (by omega)
    second actor E A0 data hsecond hnew).1
  let R := ⁅VAt Γ cp.a', Subgroup.zpowers (selected : G)⁆
  intro hmodules
  let D : Subgroup action.range :=
    ⁅SectionOne.oddCore action.range, Subgroup.zpowers (action.rangeRestrict selected)⁆ ⊔
      Subgroup.zpowers (action.rangeRestrict selected)
  have hselectedD : action.rangeRestrict selected ∈ D :=
    (show Subgroup.zpowers (action.rangeRestrict selected) ≤ D from le_sup_right)
      (Subgroup.mem_zpowers _)
  have hbound := nine_ten_predecessor_displacement_bound ctx hb predecessor neighbor
    hpred hneighbor hmodules selected hselected hnotCore action hformula hkernel hyp
      D hfactor hselectedD hsupport
  have hRU : R ≤ VAt Γ cp.a' :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr selected.property).trans
        (stabilizer_le_normalizer_v Γ cp.a'))
  obtain ⟨K, hK, hcard, hcomm⟩ := nine_ten_predecessor_large_subgroup ctx hb predecessor neighbor
    hpred hneighbor hmodules R hRU hbound.2 hbound.1 actor hactorNeighbor
  have hnot := nine_ten_predecessor_large_subgroup_not_le_first ctx (by omega) third hthird
    data.x⁻¹ hxFirst K hK hcard
  have hgeneration : ∀ n : Γ.Vertex,
      n ∈ Neighborhood Γ cp.firstStep → n ∈ Neighborhood Γ predecessor →
      (GAt Γ cp.firstStep ⊓ GAt Γ n) ⊔ Subgroup.zpowers actor = GAt Γ cp.firstStep :=
    nine_ten_prescribed_actor_common_neighbor_generation ctx.toLocalContext third second neighbor
      hthird hneighbor actor E A0 data hactorNeighbor
  exact hnot (lemma_nine_four_ambient ctx hshort third hdistance actor hactorGeometry
    data.x⁻¹ hxComm K hK hcomm hgeneration hdisplacement)

/-- Actual normalized extraction at b>3 with the same noncommuting predecessor. -/
public theorem nine_ten_normalized_noncommuting_predecessor
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length) :
    ∃ cp : CriticalPath ctx.Γ,
      cp.length = ctx.criticalPath.length ∧
      ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ cp.a'⁆ = ⊥ ∧
      (¬ ZAt ctx.Γ cp.a' ≤ VAt ctx.Γ cp.firstStep) ∧
      (¬ ZAt ctx.Γ cp.firstStep ≤ VAt ctx.Γ cp.a') ∧
      ∃ (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
        (data : NineThreeGeometricData ctx.Γ cp.firstStep second
          (VAt ctx.Γ cp.a') E A0 actor),
        IsCriticalPathOffset ctx.Γ cp 2 second ∧
        ctx.Γ.act data.x⁻¹ second = cp.a ∧
        neighbor ∈ neighborhood ctx.Γ cp.a' ∧
        actor ∈ ZAt ctx.Γ neighbor ∧
        ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥ ∧
        twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆ ∧
        ∃ (firstActor : G) (firstE firstA0 : Subgroup G)
          (firstData : NineThreeGeometricData ctx.Γ cp.a'
            (cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
            (VAt ctx.Γ cp.firstStep) firstE firstA0 firstActor),
          ctx.Γ.act firstData.x⁻¹
            (cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) = neighbor ∧
          (∀ b : G, b ∈ VAt ctx.Γ cp.firstStep → b ∉ firstA0 →
            twoResidualIn firstE ≤ ⁅twoResidualIn firstE, Subgroup.zpowers b⁆) ∧
          ∀ third : ctx.Γ.Vertex, IsCriticalPathOffset ctx.Γ cp 3 third →
            ⁅VAt ctx.Γ (ctx.Γ.act data.x⁻¹ third), ZAt ctx.Γ (cp.path
              ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)⁆ ≠ ⊥ := by
  have hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
    intro hh
    have hbound := lemma_nine_eight_ambient ctx hh
    omega
  have hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a' := by
    intro hh
    have hbound := lemma_nine_nine_ambient ctx hh
    omega
  obtain ⟨cp, hlen, hcomm, hterm, hfirst, neighbor, second, actor, E, A0, data,
    hsecond, hnew, hneighbor, hactorNeighbor, hcenters, hactorComm,
    firstActor, firstE, firstA0, firstData, hfirstNew, hfirstActors⟩ :=
    nine_ten_normalized_extraction_with_residual_witnesses ctx (by omega) hterminalNot hfirstNot
  let shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    {ctx with criticalPath := cp, commutator_eq := hcomm}
  have hshifted : 4 < shifted.criticalPath.length := by
    have hfive := nine_ten_length_ge_five ctx.toLocalContext hb
    change 5 ≤ ctx.criticalPath.length at hfive
    change 4 < cp.length
    omega
  have hmodules := nine_ten_predecessor_noncommutation shifted hshifted hterm hfirst
    neighbor second actor E A0 data hsecond hactorNeighbor hactorComm hnew hneighbor hcenters
      firstActor firstE firstA0 firstData hfirstNew hfirstActors
  refine ⟨cp, hlen, hcomm, hterm, hfirst, neighbor, second, actor, E, A0, data,
    hsecond, hnew, hneighbor, hactorNeighbor, hcenters, hactorComm,
    firstActor, firstE, firstA0, firstData, hfirstNew, hfirstActors, ?_⟩
  intro third hthird
  obtain ⟨index, hindex, rfl⟩ := hthird
  have hindexEq : (⟨3, by change 4 < cp.length at hshifted; omega⟩ : Fin (cp.length + 1)) = index :=
    Fin.ext hindex.symm
  simpa only [hindexEq] using hmodules

end Stellmacher.SectionNine
