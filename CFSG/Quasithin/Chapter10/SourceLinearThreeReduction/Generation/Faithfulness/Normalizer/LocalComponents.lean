module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalModule
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.PairQuotients
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.ModuleSize

/-!
# Large local modules detect the escaping odd-normalizer component

The fixed residual retains both simple component quotients in every nontrivial
image. Its action on a nonzero local moved module therefore has order divisible
by sixteen, forcing that module to have more than eight elements. The genuine
quasithin rank bound then centralizes the odd core. Covering uniqueness kills
the normalizer two-core, and generalized-Fitting detection gives a component
outside M moved by this same local module.

This uses local fixation only, retaining the literal fixed residual and module.
Source: Aschbacher--Smith 4.4.8--10, printed pp.620--621, in the proof of
10.2.3(2), printed p.745 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
private theorem component_four_dvd
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    4 ∣ Nat.card (L ⧸ pCore 2 L) := by
  let Q := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let e : (Q ⧸ center Q) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq
      (source_nonnormal_component_core_center D hn)).trans QuotientGroup.quotientBot
  let : IsSimpleGroup Q := e.symm.isSimpleGroup
  let P : Sylow 2 Q := Classical.choice inferInstance
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  have hlarge := Chapter1.Section02.IndexTwo.two_lt_card_sylow_of_simple_perfect P
  have htwo : 2 ≤ n := by
    by_contra hh
    have hsmall := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ 1)
    rw [←hn] at hsmall
    norm_num at hsmall
    omega
  exact (show 2 ^ 2 ∣ Nat.card P by rw [hn]; exact pow_dvd_pow 2 htwo).trans
    P.toSubgroup.card_subgroup_dvd_card

/-- The actual fixed-residual action makes every nonzero local moved module large. -/
theorem source_local_oddPrimeActor_module_card_gt_eight
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (W : Subgroup G) (hWV : W ≤ D.fullModule) (hne : W ≠ ⊥)
    (hWX : W = ⁅W,localOrbit T L⁆)
    (hNW : localJoin T L ≤ normalizer (W : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsPGroup p A)
    (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hAW : A ≤ centralizer (W : Set G))
    (hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G)) :
    8 < Nat.card W := by
  classical
  let X := localOrbit T L
  let C := X ⊓ centralizer (A : Set G)
  let F := (solvableResidual C).map C.subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (A : Set G))
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := hA.exists_card_eq
    rw [he]
    exact hp.pow
  obtain ⟨_,he,_⟩ := source_local_oddActor_cover D W hWV hWX hNW A hAC hodd hAW
  have hIW : I ≤ normalizer (W : Set G) := (sup_le
    (((map_subtype_le _).trans inf_le_left).trans (show X ≤ localJoin T L from le_sup_left))
    (inf_le_left.trans (show (T : Subgroup G) ≤ localJoin T L from le_sup_right))).trans hNW
  let f : I →* MulAut W := W.normalizerMonoidHom.comp (inclusion hIW)
  have h16 : 16 ∣ Nat.card (MulAut W) := by
    rcases source_nonnormal_oddActorResidual_hom_trivial_or_square D 4
      (component_four_dvd D hn) hn hp A hA hAC hAT f with hz | hd
    · have hFW : F ≤ centralizer (W : Set G) := by
        intro x hx w hw
        have hh := DFunLike.congr_fun hz (⟨x,hx⟩ : F)
        have hv := congrArg (fun a : MulAut W => (a ⟨w,hw⟩ : G)) hh
        change x*w*x⁻¹ = w at hv
        exact (mul_inv_eq_iff_eq_mul.mp hv).symm
      exact (hne (he.trans (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp hFW)))).elim
    · exact hd.trans (Subgroup.card_subgroup_dvd_card _)
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  obtain ⟨n,hcard⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
  by_contra hh
  have hn : n ≤ 3 := by
    by_contra hh'
    have hb := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ n)
    rw [←hcard] at hb
    norm_num at hb
    omega
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow W n hcard] at h16
  interval_cases n <;> norm_num [Fin.prod_univ_succ] at h16

/-- Local fixation puts the same module in the two-core of the normalizer overlap. -/
theorem source_local_oddActor_overlap_core
    (W : Subgroup G) (hWV : W ≤ D.fullModule)
    (hWX : W = ⁅W,localOrbit T L⁆)
    (hNW : localJoin T L ≤ normalizer (W : Set G))
    (A : Subgroup G) (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card A)) (hAW : A ≤ centralizer (W : Set G)) :
    W ≤ (D.maximalLocal ⊓ normalizer (A : Set G)).pCoreIn 2 := by
  obtain ⟨_,_,hc⟩ := source_local_oddActor_cover D W hWV hWX hNW A hAC hodd hAW
  let C := localOrbit T L ⊓ centralizer (A : Set G)
  let F := (solvableResidual C).map C.subtype
  have hF : F ≤ D.maximalLocal ⊓ normalizer (A : Set G) :=
    le_inf (((map_subtype_le _).trans inf_le_left).trans (localOrbit T L).le_normalizer)
      (((map_subtype_le _).trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _))
  exact hc.trans (pCoreIn_mono_of_normalizes hF
    (((le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_centralizer A))).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image C (solvableResidual C))))

private theorem perfect_twoPerfect {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] : IsPPerfect 2 X := by
  intro N hN hp
  let := hN
  by_contra hne
  let : Nontrivial (X ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable (X ⧸ N) inferInstance

/-- The entire odd core centralizes the local module and lies in M. -/
theorem source_local_oddPrimeActor_oddCore
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (W : Subgroup G) (hWV : W ≤ D.fullModule) (hne : W ≠ ⊥)
    (hWX : W = ⁅W,localOrbit T L⁆)
    (hNW : localJoin T L ≤ normalizer (W : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsPGroup p A)
    (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hAW : A ≤ centralizer (W : Set G))
    (hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G)) :
    let O := (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype
    ⁅W,O⁆ = ⊥ ∧ O ≤ D.maximalLocal := by
  let N := normalizer (A : Set G)
  let C := localOrbit T L ⊓ centralizer (A : Set G)
  let F := (solvableResidual C).map C.subtype
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hWN : W ≤ N := (le_centralizer_iff.mp hAW).trans (Subgroup.centralizer_le_normalizer _)
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := hA.exists_card_eq
    rw [he]
    exact hp.pow
  obtain ⟨_,he,_⟩ := source_local_oddActor_cover D W hWV hWX hNW A hAC hodd hAW
  let : Group.IsPerfect F := Group.IsPerfect.map C.subtype
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFN).symm.toMonoidHom) (subgroupOfEquivOfLe hFN).symm.surjective
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  let : IsElementaryAbelian 2 (W.subgroupOf N) := IsElementaryAbelian.subgroupOf hWN
  have heN : W.subgroupOf N = ⁅W.subgroupOf N,F.subgroupOf N⁆ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWN,map_subgroupOf_eq_of_le hFN]
    exact he
  have hcN : 8 < Nat.card (W.subgroupOf N) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv]
    exact source_local_oddPrimeActor_module_card_gt_eight D hn W hWV hne hWX hNW hp A hA hAC hAW hAT
  have hh := ChapterA.large_elementary_commutator_centralizes_oddCore
    (D.simpleQTKE.quasithin.subgroup N) (F.subgroupOf N) (W.subgroupOf N)
    perfect_twoPerfect hcN heN
  have hm := congrArg (Subgroup.map N.subtype) hh
  have hcomm : ⁅W,(pPrimeCore 2 N).map N.subtype⁆ = ⊥ := by
    simpa only [map_commutator,map_subgroupOf_eq_of_le hWN,Subgroup.map_bot] using hm
  have hWM : normalizer (W : Set G) ≤ D.maximalLocal :=
    normalizer_le_of_unique_maximalTwoLocal
      (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.2
      (IsElementaryAbelian.isPGroup 2 W) hne hNW
  exact ⟨hcomm,((le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (Subgroup.centralizer_le_normalizer _)).trans hWM⟩

/-- An escaping normalizer has a genuine component moved by the local module.
The component, its full center, and the original fixed residual are retained. -/
theorem source_local_oddPrimeActor_moved_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (W : Subgroup G) (hWV : W ≤ D.fullModule) (hne : W ≠ ⊥)
    (hWX : W = ⁅W,localOrbit T L⁆)
    (hNW : localJoin T L ≤ normalizer (W : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) [IsMulCommutative A] (hAne : A ≠ ⊥) (hA : IsPGroup p A)
    (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hAW : A ≤ centralizer (W : Set G))
    (hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ D.maximalLocal) :
    pCore 2 (normalizer (A : Set G)) = ⊥ ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧
        ⁅K,W.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal ∧
        pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
        ((solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
          (localOrbit T L ⊓ centralizer (A : Set G)).subtype).subgroupOf
            (normalizer (A : Set G)) ≤ normalizer (K : Set (normalizer (A : Set G))) ∧
        W.subgroupOf (normalizer (A : Set G)) ≤ normalizer (K : Set (normalizer (A : Set G))) := by
  let N := normalizer (A : Set G)
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (A : Set G)).subtype
  let Y := D.maximalLocal.subgroupOf N
  have hc : pCore 2 N = ⊥ := by
    by_contra hcore
    exact hout (source_local_oddPrimeActor_normalizer_of_twoCore D hn W hWV hne hWX hNW
      hp A hA hAC hAW hAT hcore)
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := hA.exists_card_eq
    rw [he]
    exact hp.pow
  have hWN : W ≤ N := (le_centralizer_iff.mp hAW).trans (Subgroup.centralizer_le_normalizer _)
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hvcore := source_local_oddActor_overlap_core D W hWV hWX hNW A hAC hodd hAW
  have hk : IsPGroup 2 N.subtype.ker := by
    rw [N.subtype.ker_eq_bot N.subtype_injective]
    exact IsPGroup.of_bot
  have hvY : W.subgroupOf N ≤ Y.pCoreIn 2 := by
    apply (Subgroup.map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hWN,map_pCoreIn_of_ker_isPGroup N.subtype hk]
    simpa only [Y,subgroupOf_map_subtype,N] using hvcore
  have hvne : W.subgroupOf N ≠ ⊥ := by
    intro hb
    have hh := congrArg (map N.subtype) hb
    rw [map_subgroupOf_eq_of_le hWN,Subgroup.map_bot] at hh
    exact hne hh
  have hvo : ⁅W.subgroupOf N,pPrimeCore 2 N⁆ = ⊥ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWN,Subgroup.map_bot]
    exact (source_local_oddPrimeActor_oddCore D hn W hWV hne hWX hNW hp A hA hAC hAW hAT).1
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  have hWp : IsPGroup 2 W := (IsElementaryAbelian.isPGroup 2 D.fullModule).to_le hWV
  obtain ⟨K,hK,hm,ho⟩ := exists_component_moved_outside_of_centralizes_oddCore
    (W.subgroupOf N) Y hWp.comap_subtype hvne hc hvo hvY
  have houtK : ¬ K.map N.subtype ≤ D.maximalLocal := fun he => ho (map_le_iff_le_comap.mp he)
  have hKc : pCore 2 K = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hK.1,hc,MonoidHom.comap_bot]
    exact K.subtype.ker_eq_bot K.subtype_injective
  obtain ⟨_,hqt,_⟩ := oddNormalizer_properQTK D.simpleQTKE A hAne
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have heven : 2 ∣ Nat.card K := by
    by_contra hnot
    exact Group.IsPerfect.not_isSolvable K
      (_root_.odd_order_theorem K (Nat.not_even_iff_odd.mp (by
        simpa only [even_iff_two_dvd] using hnot)))
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFN).symm.toMonoidHom) (subgroupOfEquivOfLe hFN).symm.surjective
  have heW : W.subgroupOf N = ⁅W.subgroupOf N,F.subgroupOf N⁆ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWN,map_subgroupOf_eq_of_le hFN]
    exact (source_local_oddActor_cover D W hWV hWX hNW A hAC hodd hAW).2.1
  obtain ⟨hFK,hWK⟩ := hK.perfect_commutator_normalizes_of_quasithin hqt heven
    (F.subgroupOf N) (W.subgroupOf N) heW
  exact ⟨hc,K,hK,hK.commutator_eq_self_of_normalizes hWK hm,houtK,hKc,
    source_oddNormalizer_component_theoremB D A hAne K hK,hFK,hWK⟩

end CFSG.Quasithin.Chapter10
