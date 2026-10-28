module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeConstructionGeometry
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy

public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.SpecificGroups.Suzuki.OddSubgroups
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.BenderHall.Reduction

/-!
# Selecting the single rank-one residual before Cartan normalization

Rank-one Sylow-normalizer uniqueness identifies the Borel of the actual
residual K = O²(H) with N_G(L) ∩ K. Its singleton family therefore satisfies
the complete right geometry. A quasisimple intrinsic quotient makes K an
actual C-component, giving the full prime-pair LocalData without a right
selection callback. Since T normalizes K, a nonzero generated core would
contradict the proved strictness of N_T(K) < T. Thus the literal pair lies
in the zero-core branch and satisfies genuine F.1.1.

For the single PSL₂ and Suzuki source rows, the canonical comparison from
the component image in H/O₂(H) to its image in H/core_H(M) is central.
Cyclic odd Sylow transfer and the trivial two-core make this comparison
injective after the supplied model marking. This identifies the intrinsic
quotient and supplies the preceding construction directly from E.2.2,
including the small exceptional covering parameters. No equality of the
source kernel with O₂(H) is assumed in these single-component rows.

The exchanged, unitary and rank-two source selections, the zero-core model
exclusions, higher-field reduction and full conditional normalization remain
with qt-d-1222-rankone-cartan-local-to-global. This module completes the
single linear/Suzuki construction, not the entire source theorem.
Source: Aschbacher–Smith E.2.2, F.1.3(1), I.1.2, 5.1.10 and 5.2.2,
printed pp.215–216,259–260,407,634,646–648 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem residual_borel_facts
    {T : Sylow 2 G} {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hm : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H))) :
    ChapterF.Source.RankOneBorelFacts (residual H) (T : Subgroup G) := by
  let e : pResidual 2 H ≃* residual H :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  obtain ⟨P,hP⟩ := exists_sylow_component (hTH.trans (le_normalizer_residual H))
  exact ChapterF.Source.rankOneBorelFacts_of_sylow _ _ P hP
    (ChapterF.Source.rankOneSylowFacts_of_rankOneQuotient (hm.of_equiv eq.symm) P)

/-- The actual residual Borel is the overlap with the original maximal local group. -/
theorem rankOne_residual_borel_eq_overlap
    {T : Sylow 2 G} {L H : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hm : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H))) :
    ChapterF.Source.borel (residual H) (T : Subgroup G) =
      normalizer (L : Set G) ⊓ residual H := by
  let K := residual H
  let U := (T : Subgroup G) ⊓ K
  let J := H ⊓ normalizer (U : Set G)
  have hf := residual_borel_facts hH.1.1.2 hm
  have hKH : K ≤ H := map_subtype_le _
  have hTJ : (T : Subgroup G) ≤ J := le_inf hH.1.1.2
    ((le_inf (T : Subgroup G).le_normalizer
      (hH.1.1.2.trans (le_normalizer_residual H))).trans inf_normalizer_le_normalizer_inf)
  have hJH : J < H := lt_of_le_of_ne inf_le_left (by
    intro he
    apply hf.proper.not_ge
    have hHN : H ≤ normalizer (U : Set G) := by
      rw [←he]
      exact inf_le_right
    exact le_inf le_rfl (hKH.trans hHN))
  have hBM : ChapterF.Source.borel K (T : Subgroup G) ≤ normalizer (L : Set G) :=
    (le_inf (inf_le_left.trans hKH) inf_le_right).trans
      (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)
  apply le_antisymm (le_inf hBM inf_le_left)
  apply hf.unique_maximal
  · exact le_inf (inf_le_left.trans hTL) inf_le_right
  · exact lt_of_le_of_ne inf_le_right (fun he =>
      residual_not_le T H _ hH.1.1.2 hTL hH.1.2 (he ▸ inf_le_left))

/-- In the single rank-one residual row, the entire right family is the singleton residual. -/
theorem rankOne_residual_geometry
    {T : Sylow 2 G} {L H : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hm : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H))) :
    RightGeometry T L H {residual H} := by
  have hb := rankOne_residual_borel_eq_overlap hTL hH hm
  let e : pResidual 2 H ≃* residual H :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  refine {
    nonempty := ⟨residual H,Set.mem_singleton _⟩
    small := by simp
    two_closed := hb ▸ inf_le_right
    invariant := ?_
    le_residual := ?_
    generates := ?_
    sylow := ?_
    quotient := ?_
    S_normalizes := ?_
    overlap := ?_ }
  · intro g hg _ R hR
    have hR := Set.mem_singleton_iff.mp hR
    subst R
    exact Set.mem_singleton_iff.mpr (mem_normalizer_iff_map_conj_eq.mp hg)
  · intro R hR
    exact (Set.mem_singleton_iff.mp hR).le
  · intro R hR
    rw [Set.mem_singleton_iff.mp hR]
    exact residual_sup_sylow T H hH.1.1.2
  · intro R hR
    rw [Set.mem_singleton_iff.mp hR]
    exact exists_sylow_component (hH.1.1.2.trans (le_normalizer_residual H))
  · intro R hR
    rw [Set.mem_singleton_iff.mp hR]
    exact hm.of_equiv eq.symm
  · intro R hR
    rw [Set.mem_singleton_iff.mp hR]
    exact (sourceS_le_sylow hTL hH.1.1.2).trans
      (hH.1.1.2.trans (le_normalizer_residual H))
  · intro R hR
    rw [Set.mem_singleton_iff.mp hR]
    exact hb

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- A quasisimple rank-one quotient selects the actual residual as the right factor. -/
theorem rankOne_residual_rightData
    {T : Sylow 2 G} {L H A B : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hm : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)))
    (hqs : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H))) :
    RightData T L H B (residual H) := by
  let := hqs
  have hC : (pResidual 2 H).IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (Subgroup.Normal.isSubnormal inferInstance) (isPPerfect_pResidual 2)
  have hC' : ((residual H).subgroupOf H).IsCComponent := by
    change (((pResidual 2 H).map H.subtype).comap H.subtype).IsCComponent
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  exact (Global.rankOne_residual_geometry hTL hH hm).primeRightData_of_component
    c hTL hH (Set.mem_singleton _) hC'

/-- The selected residual forces the zero-core branch and satisfies genuine F.1.1. -/
theorem rankOne_residual_prime_pair
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hm : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)))
    (hqs : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H))) :
    LocalData T L H B D (residual H) ∧
      (generated L H D (residual H)).pCoreIn 2 = ⊥ ∧
      ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,residual H]
        (Global.sourceS L H) := by
  let d := (rankOne_residual_rightData h.sylow_normalizes hH c hm hqs).localData h hH c hd
  have hz : (generated L H D (residual H)).pCoreIn 2 = ⊥ := by
    by_contra hz
    exact (d.normalizingSylow_lt hH.1.1.2 c hd hz).not_ge
      (le_inf le_rfl (hH.1.1.2.trans (le_normalizer_residual H)))
  exact ⟨d,hz,d.hypothesisF11 h hH c hd hz⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open scoped MatrixGroups
variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem single_source_comparison
    {M C U : Subgroup X} (hO : pCore 2 X ≤ sourceKernel M)
    (hc : SingleClauses M C U) :
    ∃ r : actorImage C →* sourceImage M C,
      Function.Surjective r ∧ r.ker ≤ center (actorImage C) := by
  let q := QuotientGroup.map (pCore 2 X) (sourceKernel M) (MonoidHom.id X) hO
  let r : actorImage C →* sourceImage M C :=
    (q.comp (actorImage C).subtype).codRestrict _ (by
      rintro ⟨x,k,hk,rfl⟩
      exact ⟨k,hk,rfl⟩)
  refine ⟨r,?_,?_⟩
  · rintro ⟨x,k,hk,rfl⟩
    exact ⟨⟨QuotientGroup.mk' (pCore 2 X) k,k,hk,rfl⟩,rfl⟩
  · intro a ha
    obtain ⟨k,hk,hka⟩ := a.property
    have hkj : k ∈ sourceKernel M := by
      apply (QuotientGroup.eq_one_iff k).mp
      have hh := congrArg Subtype.val ha
      change q a.val = 1 at hh
      rw [←hka] at hh
      exact hh
    have hz : a.val ∈ (center (actorImage C)).map (actorImage C).subtype := by
      rw [←hc.kernel_center]
      exact ⟨k,hkj,hka⟩
    obtain ⟨z,hz,hza⟩ := hz
    exact (show z = a from Subtype.ext hza) ▸ hz

/-- The single linear/Suzuki source marking identifies the intrinsic two-core quotient.
Cyclic odd Sylow transfer removes the central comparison kernel, including field four. -/
theorem single_linear_suzuki_component_quotient
    {M C U : Subgroup X} {f : ℕ} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hO : pCore 2 X ≤ sourceKernel M)
    (hc : SingleClauses M C U) (hm : ExchangedModel M C f) :
    ChapterF.Source.IsRankOneModel (C ⧸ pCore 2 C) := by
  let eC := cComponentTwoCoreQuotientEquiv hC
  let := hqs
  let : IsQuasisimple (actorImage C) := IsQuasisimple.of_mulEquiv eC
  have hz : pCore 2 (actorImage C) = ⊥ := by
    change pCore 2 (C.map (QuotientGroup.mk' (pCore 2 X))) = ⊥
    rw [←pCore_map_iso 2 eC,pCore_quotient_pCore_eq_bot,Subgroup.map_bot]
  obtain ⟨r,hr,hrc⟩ := single_source_comparison hO hc
  rcases hm with ⟨F,_,_,_,hf,hF,e,_⟩ | ⟨m,hm,_,e,_⟩
  · let c : PerfectCentralCovering.Cover (actorImage C) PSL(2,F) := {
      toMonoidHom := e.toMonoidHom.comp r
      surjective := e.surjective.comp hr
      isPerfect := inferInstance
      ker_le_center := fun x hx => hrc (e.injective (hx.trans e.map_one.symm)) }
    have hi := c.injective_of_pCore_eq_bot_of_cyclic_sylow hz (by
      intro p hp hp2 P
      let : Fact p.Prime := ⟨hp⟩
      let j := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
      exact Matrix.SL2.odd_pGroup_isCyclic_of_injective P.isPGroup' hp2
        (j.toMonoidHom.comp (P : Subgroup PSL(2,F)).subtype)
        (j.injective.comp (P : Subgroup PSL(2,F)).subtype_injective))
    exact .linear f (by omega) ⟨F,inferInstance,inferInstance,hF,
      ⟨eC.trans (MulEquiv.ofBijective c.toMonoidHom ⟨hi,c.surjective⟩)⟩⟩
  · let c : PerfectCentralCovering.Cover (actorImage C)
        (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := {
      toMonoidHom := e.toMonoidHom.comp r
      surjective := e.surjective.comp hr
      isPerfect := inferInstance
      ker_le_center := fun x hx => hrc (e.injective (hx.trans e.map_one.symm)) }
    have hi := c.injective_of_pCore_eq_bot_of_cyclic_sylow hz (by
      intro p hp hp2 P
      let : Fact p.Prime := ⟨hp⟩
      exact BenderSuzuki.MatrixGroups.suzukiSylow_isCyclic_of_ne_two (by omega) hp2 P)
    exact .suzuki m ⟨eC.trans (MulEquiv.ofBijective c.toMonoidHom ⟨hi,c.surjective⟩)⟩

variable {G : Type*} [Group G] [Finite G]

/-- The actual single linear/Suzuki source branch constructs the local pair and its zero-core amalgam. -/
theorem single_linear_suzuki_prime_pair
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f) :
    LocalData T L H B D (residual H) ∧
      (generated L H D (residual H)).pCoreIn 2 = ⊥ ∧
      ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,residual H]
        (Global.sourceS L H) := by
  have hO : pCore 2 H ≤ sourceKernel ((normalizer (L : Set G)).subgroupOf H) := by
    apply Subgroup.normal_le_normalCore.mpr
    exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)).trans
      (comap_mono h.sylow_normalizes)
  have hr := single_linear_suzuki_component_quotient hC hqs hO hc hm
  have he : C = pResidual 2 H :=
    BenderHall.SingleClauses.component_eq_residual (S := T.subtype hH.1.1.2) hc hC
  subst C
  exact rankOne_residual_prime_pair h hH c hd hr hqs

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
