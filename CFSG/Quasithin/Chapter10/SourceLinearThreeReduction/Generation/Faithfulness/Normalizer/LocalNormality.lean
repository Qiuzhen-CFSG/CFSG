module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalComponents

/-!
# Normality of the component detected by local fixation

Inner projection of the actual fixed residual produces a perfect subgroup
with noncentral two-core whenever the detected component escapes M. The
five possible nonnormal component rows have central two-cores in every
perfect subgroup, so that component is normal. All covering centers and
the literal odd-normalizer maps are retained. Only local module fixation
is used in the projection.

Source: Aschbacher--Smith 4.4.9--11, printed p.621, as used by10.2.3(2),
printed p.745 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterA.QTComponents
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The literal residual projects onto a perfect subgroup with noncentral two-core. -/
theorem source_local_oddActor_noncentral_perfect_subgroup
    (W : Subgroup G) (hWV : W ≤ D.fullModule) (hne : W ≠ ⊥)
    (hWX : W = ⁅W,localOrbit T L⁆)
    (hNW : localJoin T L ≤ normalizer (W : Set G))
    (A : Subgroup G) (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card A)) (hAW : A ≤ centralizer (W : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal)
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (A : Set G)).subtype).subgroupOf
          (normalizer (A : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (A : Set G)))) :
    ∃ P : Subgroup (normalizer (A : Set G)), P ≤ K ∧ Group.IsPerfect P ∧
      ⁅P.pCoreIn 2,P⁆ ≠ ⊥ := by
  let N := normalizer (A : Set G)
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (A : Set G)).subtype
  let U := W.subgroupOf N
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hWN : W ≤ N := (le_centralizer_iff.mp hAW).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,hm,hWF⟩ := source_local_oddActor_cover D W hWV hWX hNW A hAC hodd hAW
  have hUF : U ≤ F.subgroupOf N := subgroupOf_mono N (hWF.trans (pCoreIn_le 2 F))
  have hmove : U = ⁅U,F.subgroupOf N⁆ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWN,map_subgroupOf_eq_of_le hFN]
    exact hm
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  have hWp : IsPGroup 2 W := (IsElementaryAbelian.isPGroup 2 D.fullModule).to_le hWV
  have hWM : normalizer (W : Set G) ≤ D.maximalLocal :=
    normalizer_le_of_unique_maximalTwoLocal
      (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.2 hWp hne hNW
  have hnc : ¬ U ≤ centralizer (K : Set N) := by
    intro hc
    apply houtK
    apply le_trans ?_ hWM
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rintro _ ⟨k,hk,rfl⟩ w hw
    exact congrArg Subtype.val (hc (show (⟨w,hWN hw⟩ : N) ∈ U from hw) k hk).symm
  let := source_oddNormalizer_residual_perfect (T := T) (L := L) A
  obtain ⟨P,Q,hPK,_,hP,_,_,_,hnc,_⟩ :=
    exists_perfect_projection_with_noncentral_core K (centralizer (K : Set N))
      (F.subgroupOf N) U (le_centralizer_iff.mp le_rfl) hinner hUF hWp.comap_subtype hmove hnc
  exact ⟨P,hPK,hP,hnc⟩

private theorem projected_core_central
    {N : Type*} [Group N] [Finite N]
    (K P : Subgroup N) (hPK : P ≤ K)
    (hcentral : pCore 2 P ≤ (center K).comap (inclusion hPK)) :
    ⁅P.pCoreIn 2, P⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro x ⟨u, hu, rfl⟩ y hy
  exact congrArg Subtype.val (mem_center_iff.mp (hcentral hu) ⟨y,hPK hy⟩)

private theorem core_central_of_quotient_kernel
    {N S : Type*} [Group N] [Finite N] [Group S]
    (K P : Subgroup N) (hPK : P ≤ K) (e : K ⧸ center K ≃* S)
    (hk : pCore 2 P ≤ ((e.toMonoidHom.comp (QuotientGroup.mk' (center K))).comp
      (inclusion hPK)).ker) : ⁅P.pCoreIn 2,P⁆ = ⊥ := by
  apply projected_core_central K P hPK
  intro x hx
  exact (QuotientGroup.eq_one_iff (inclusion hPK x)).mp
    (e.map_eq_one_iff.mp (hk hx))

private theorem suzuki_perfect_core_le_ker
    {A : Type*} [Group A] [Group.IsPerfect A]
    {m : ℕ} (hm : 0 < m)
    (f : A →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : pCore 2 A ≤ f.ker := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hbot : pCore 2 f.range = ⊥ := by
    by_contra hne
    let : Nontrivial f.range := (Subgroup.nontrivial_iff_ne_bot _).mpr (by
      intro he
      have : Subsingleton f.range := by rw [he]; infer_instance
      exact hne (Subsingleton.elim _ _))
    let : Group.IsNilpotent (pCore 2 f.range) := pCore_isNilpotent
    have hs := BenderSuzuki.MatrixGroups.suzukiSubgroup_isSolvable_of_solvable_normal
      hm f.range (pCore 2 f.range) hne
    exact Group.IsPerfect.not_isSolvable f.range hs
  have him : (pCore 2 A).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map f.rangeRestrict
      f.rangeRestrict_surjective, pCore_isPGroup.map f.rangeRestrict⟩
  rw [hbot] at him
  have hk := (Subgroup.map_eq_bot_iff _).mp (bot_unique him)
  intro a ha
  exact congrArg Subtype.val (hk ha)


/-- The actual detected component is normal under the weaker local-fixation hypotheses. -/
theorem source_local_oddActor_component_normal
    (W : Subgroup G) (hWV : W ≤ D.fullModule) (hne : W ≠ ⊥)
    (hWX : W = ⁅W,localOrbit T L⁆)
    (hNW : localJoin T L ≤ normalizer (W : Set G))
    (A : Subgroup G) [IsMulCommutative A] (hAne : A ≠ ⊥)
    (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card A)) (hAW : A ≤ centralizer (W : Set G))
    (hcore : pCore 2 (normalizer (A : Set G)) = ⊥)
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (A : Set G)).subtype).subgroupOf
          (normalizer (A : Set G)) ≤ normalizer (K : Set (normalizer (A : Set G)))) :
    K.Normal := by
  classical
  by_contra hnK
  obtain ⟨_,hqt,hkg⟩ := oddNormalizer_properQTK D.simpleQTKE A hAne
  have hi := source_oddNormalizer_nonnormal_component_inner D A hAne K hK hnK hFK
  obtain ⟨P,hPK,hP,hnc⟩ := source_local_oddActor_noncentral_perfect_subgroup
    D W hWV hne hWX hNW A hAC hodd hAW K houtK hi
  let := hP
  have hunitary {f : ℕ} (hf : 0 < f)
      (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 (2 ^ f)) : False := by
    let j : P →* K ⧸ center K := (QuotientGroup.mk' (center K)).comp (inclusion hPK)
    have hk := ChapterF.Source.Unitary.perfect_hom_twoCore_le_ker hf hm j
    exact hnc (projected_core_central K P hPK (fun u hu =>
      (QuotientGroup.eq_one_iff (inclusion hPK u)).mp (hk hu)))
  have hz : center K = ⊥ := by
    by_contra hz
    obtain ⟨n,hn,_,hm⟩ := nonnormal_centered_projectiveUnitary hqt hkg hcore K hK hnK hz
    exact hunitary (by omega) hm
  let j : (K ⧸ center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  have hr : OddRankBudget K := fun r hp ho =>
    hK.local_add_ordinary_rank_le_two_of_nonnormal_centerless hqt hnK hz r hp ho
  have hb : OddRankBudget (K ⧸ center K) := OddRankBudget.of_mulEquiv hr j
  have hm := nonnormal_model_of_budget_of_remaining_local remainingLocalInput hb
    (nonnormal_centralQuotient_model hqt hkg K hK hnK)
  cases hm with
  | linear_even n hn he =>
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := he
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hc)
    let q : P →* Theory.PSL2.Group F :=
      (e.toMonoidHom.comp (QuotientGroup.mk' (center K))).comp (inclusion hPK)
    let qsl := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm.toMonoidHom.comp q
    have hqsl := Matrix.SpecialLinearGroup.perfect_hom_twoCore_le_ker qsl
    apply hnc
    apply core_central_of_quotient_kernel K P hPK e
    intro x hx
    exact (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm.map_eq_one_iff.mp (hqsl hx)
  | suzuki m hm he =>
    let q := (he.some.toMonoidHom.comp (QuotientGroup.mk' (center K))).comp (inclusion hPK)
    exact hnc (core_central_of_quotient_kernel K P hPK he.some
      (suzuki_perfect_core_le_ker hm q))
  | linear_odd q ho he =>
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := he
    let f := (e.toMonoidHom.comp (QuotientGroup.mk' (center K))).comp (inclusion hPK)
    exact hnc (core_central_of_quotient_kernel K P hPK e
      (Theory.PSL2.odd_perfect_hom_twoCore_le_ker (hc.symm ▸ ho) f))
  | janko he =>
    let e := he.some
    let q : P →* Janko1.Model :=
      (e.toMonoidHom.comp (QuotientGroup.mk' (center K))).comp (inclusion hPK)
    let f : PerfectCentralCovering.Cover P q.range := {
      toMonoidHom := q.rangeRestrict
      surjective := q.rangeRestrict_surjective
      isPerfect := hP
      ker_le_center := by
        intro p hp
        have hh : q p = 1 := congrArg Subtype.val hp
        have hz : inclusion hPK p ∈ center K :=
          (QuotientGroup.eq_one_iff _).mp (e.map_eq_one_iff.mp hh)
        apply mem_center_iff.mpr
        intro y
        apply Subtype.ext
        exact congrArg (fun z : K => (z : normalizer (A : Set G)))
          (mem_center_iff.mp hz (inclusion hPK y)) }
    let : Group.IsPerfect q.range := Group.IsPerfect.range q
    have him : (pCore 2 P).map q.rangeRestrict ≤ pCore 2 q.range :=
      le_sSup ⟨(inferInstance : (pCore 2 P).Normal).map q.rangeRestrict
        q.rangeRestrict_surjective,pCore_isPGroup.map q.rangeRestrict⟩
    have hc : pCore 2 P ≤ center P := by
      rw [←f.comap_center]
      exact map_le_iff_le_comap.mp
        (him.trans (Janko1.perfect_subgroup_pCore_two_le_center q.range))
    apply hnc
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rintro x ⟨u,hu,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp (hc hu) ⟨y,hy⟩)
  | unitary n hn he => exact hunitary hn he

end CFSG.Quasithin.Chapter10
