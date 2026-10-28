module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.ChosenResidualStar
public import Theory.GroupTheory.PResidual.CyclicConjugateImage
public import Theory.GroupTheory.QuotientIntersection
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimeRankProduct

/-!
# Faithful star images of cyclic Case II residuals

The original residual is the two-residual of the intersection core's span
under O²(M₀)T. Its seed centralizes the chosen action kernel in M/O₂(M).
Relative cyclic-image transfer therefore makes the star residual faithful,
so its order is exactly the order of the literal action image.

When that image has order three, the star residual and the centralizer have
trivial intersection and commute. Rank addition and quasithinness give
three-rank at most one for C_M(V). This supplies the cubic branch of the
15.2.4 obstruction without requiring normality of Y or the stronger Sylow
structure from15.2.3.

Source: Aschbacher--Smith15.2.3(1),(5) and15.2.4, printed pp.1105--1106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem residual_notation {D : Type*} [Group D] [Finite D] (H : Subgroup D) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN,n,hn⟩
    exact ⟨hN,IsPGroup.of_card hn⟩
  · rintro ⟨hN,hp⟩
    exact ⟨hN,IsPGroup.iff_card.mp hp⟩

/-- Cyclic action image forces the literal chosen residual kernel into O₂(M). -/
theorem source_chosen_cyclic_kernel_le_core (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hcyclic : IsCyclic (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict)) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    Y.subgroupOf M ⊓ (actionHom M V hV.normalized).ker ≤ pCore 2 M := by
  let f := (actionHom M V hV.normalized).rangeRestrict
  let q := QuotientGroup.mk' (pCore 2 M)
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let R := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
  let B := (twoResidualAmbient (chosenStarredPreimage M V hV.normalized) ⊔
    (T : Subgroup G)).subgroupOf M
  have hcore : pCore 2 M ≤ f.ker := by
    simpa only [f,MonoidHom.ker_rangeRestrict] using source_chosen_core_le_kernel T hTM hV
  let g := QuotientGroup.lift (pCore 2 M) f hcore
  have hcomp : g.comp q = f := rfl
  have hker : g.ker = f.ker.map q := QuotientGroup.ker_lift _ _ _
  have hCeq : (M ⊓ centralizer (V : Set G)).subgroupOf M = f.ker := by
    rw [show f = (actionHom M V hV.normalized).rangeRestrict from rfl,
      MonoidHom.ker_rangeRestrict,actionHom_ker]
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
  have hcentral : R.map q ≤ centralizer (g.ker : Set (M ⧸ pCore 2 M)) := by
    rw [hker,← hCeq]
    exact le_sup_left.trans (source_chosen_lemma_15_2_3_5 T hTM hu hV)
  have hTMc : (T : Subgroup G) ≤ Mc := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hRT : (M ⊓ Mc).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf hTM hTMc))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le (le_inf hTM hTMc)] using hh
  have hRB : R.map q ≤ B.map q := map_mono (comap_mono (hRT.trans le_sup_right))
  have hY : (Y.subgroupOf M).map q =
      (pResidual 2 (conjugateSpanBy (R.map q) (B.map q))).map
        (conjugateSpanBy (R.map q) (B.map q)).subtype := by
    rw [source_caseIIResidual_image T hTM (map_subtype_le _) q, residual_notation]
  have hR : IsPGroup 2 (R.map q) := (isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype.map q
  have hcyclic' : IsCyclic (((Y.subgroupOf M).map q).map g) := by
    rw [map_map,hcomp]
    exact hcyclic
  have hfaithful : Disjoint ((Y.subgroupOf M).map q) g.ker := by
    rw [hY] at hcyclic' ⊢
    let := hcyclic'
    exact disjoint_twoResidual_conjugateSpan_ker_of_cyclic_image
      g (R.map q) (B.map q) hRB hR hcentral
  change Y.subgroupOf M ⊓ (actionHom M V hV.normalized).ker ≤ pCore 2 M
  intro x hx
  have hz : q x = 1 := disjoint_def.mp hfaithful (mem_map_of_mem q hx.1)
    (show q x ∈ g.ker from (show f x = 1 from Subtype.ext hx.2))
  exact (QuotientGroup.eq_one_iff x).mp hz

/-- Passing a cyclic residual through the literal star quotient preserves its action-image order. -/
theorem source_chosen_cyclic_star_card (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hcyclic : IsCyclic (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict)) :
    let Y := (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M
    Nat.card (Y.map (QuotientGroup.mk' (pCore 2 M))) =
      Nat.card (Y.map (actionHom M V hV.normalized).rangeRestrict) := by
  let A := (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M
  let f := (actionHom M V hV.normalized).rangeRestrict
  let q := QuotientGroup.mk' (pCore 2 M)
  have hbound := source_chosen_cyclic_kernel_le_core T hTM hu hV hcyclic
  have hcore := source_chosen_core_le_kernel T hTM hV
  have he : A ⊓ f.ker = A ⊓ pCore 2 M := by
    rw [show f = (actionHom M V hV.normalized).rangeRestrict from rfl,
      MonoidHom.ker_rangeRestrict]
    exact le_antisymm (le_inf inf_le_left hbound) (inf_le_inf_left A hcore)
  change Nat.card (A.map q) = Nat.card (A.map f)
  rw [← relIndex_ker,← relIndex_ker]
  rw [show q.ker = pCore 2 M from QuotientGroup.ker_mk' _]
  rw [← inf_relIndex_left A (pCore 2 M),← inf_relIndex_left A f.ker,he]

/-- The cubic-image branch has centralizer three-rank at most one, without an Omega hypothesis. -/
theorem source_chosen_cubic_centralizer_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 3) :
    primeRank 3 (M ⊓ centralizer (V : Set G) : Subgroup G) ≤ 1 := by
  let f := (actionHom M V hV.normalized).rangeRestrict
  let q := QuotientGroup.mk' (pCore 2 M)
  let Y := (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M
  let A := Y.map q
  let C := f.ker.map q
  have hcyclic : IsCyclic (Y.map f) := isCyclic_of_prime_card hcard
  have hcore : pCore 2 M ≤ f.ker := by
    simpa only [f,MonoidHom.ker_rangeRestrict] using source_chosen_core_le_kernel T hM.2 hV
  have hbound : Y ⊓ f.ker ≤ pCore 2 M := by
    simpa only [f,MonoidHom.ker_rangeRestrict] using
      source_chosen_cyclic_kernel_le_core T hM.2 hu hV hcyclic
  have hd : Disjoint A C := by
    rw [disjoint_iff]
    change Y.map q ⊓ f.ker.map q = ⊥
    rw [← map_inf_of_ker_le q Y f.ker (by rwa [QuotientGroup.ker_mk'])]
    rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hbound
  have hac : A ≤ centralizer (C : Set (M ⧸ pCore 2 M)) := by
    have hCeq : (M ⊓ centralizer (V : Set G)).subgroupOf M = f.ker := by
      rw [show f = (actionHom M V hV.normalized).rangeRestrict from rfl,
        MonoidHom.ker_rangeRestrict,actionHom_ker]
      ext x
      exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
    have hh := source_chosen_lemma_15_2_3_5 T hM.2 hu hV
    rw [hCeq] at hh
    exact le_sup_right.trans hh
  have hc : Nat.card A = 3 := (source_chosen_cyclic_star_card T hM.2 hu hV hcyclic).trans hcard
  have hrank : primeRank 3 (M ⧸ pCore 2 M) ≤ 2 := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 M) pCore_isPGroup]
    exact (hG.twoLocal_sqtk hM.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  have hCr : primeRank 3 C ≤ 1 := by
    have hAr : 1 ≤ primeRank 3 A := by
      by_contra h
      have hz : primeRank 3 A = 0 := by omega
      exact (PrimeRank.eq_zero_iff_not_dvd_card.mp hz) (hc ▸ dvd_rfl)
    have he := primeRank_sup_eq_add_of_disjoint_commuting A C hd hac 3
    have hr := (Theory.GroupTheory.primeRank_le_of_injective 3 (A ⊔ C).subtype
      (A ⊔ C).subtype_injective).trans hrank
    omega
  have hqk : IsPGroup 2 (q.subgroupMap f.ker).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  obtain ⟨k,hk⟩ := hqk.exists_card_eq
  have hCp : Nat.Coprime 3 (Nat.card (q.subgroupMap f.ker).ker) := by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have he := primeRank_eq_of_surjective_of_coprime 3 (q.subgroupMap f.ker)
    (q.subgroupMap_surjective f.ker) hCp
  have hCmap : f.ker.map M.subtype = M ⊓ centralizer (V : Set G) := by
    rw [show f = (actionHom M V hV.normalized).rangeRestrict from rfl,
      MonoidHom.ker_rangeRestrict,actionHom_ker,subgroupOf_map_subtype,inf_comm]
  have he2 := primeRank_equiv 3
    ((f.ker.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hCmap))
  change primeRank 3 f.ker = primeRank 3 C at he
  omega
end CFSG.Quasithin.Chapter15.Section02
