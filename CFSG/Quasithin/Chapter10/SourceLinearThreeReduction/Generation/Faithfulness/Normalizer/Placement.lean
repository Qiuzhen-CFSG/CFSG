module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.ActionKernel
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentProjection
public import Theory.GroupTheory.ComponentOrbitInner
public import Theory.GroupTheory.EvenCentralizerFixedInvolution
public import Theory.GroupTheory.GeneralizedFitting.OddComponentCentralizer

/-!
# Placement of the literal fixed residual in an odd-normalizer component

The original uniqueness subgroup is F N_T(B), where F=C_{L₀}(B)^∞.
Inner action projects the full module into K and its centralizer. Uniqueness
kills the centralizer projection. The faithful local action kernel then
makes F intersect C_N(K) trivially. If C_N(K) were even, N_T(B) would fix
an involution centralized by F; uniqueness would force K into M. Thus
C_N(K) is the odd core and the perfect residual lies in K.

This proves the placement step without an A₅ marking. Covering uniqueness
and inner action remain explicit earlier inputs, to be discharged by the
same owner qt-d-10-nona5-hall-faithfulness. No normalizer-containment or
Hall-faithfulness conclusion is assumed.
Source: Aschbacher--Smith, 4.4.10--11, printed p.621 (combined manuscript
of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original full module lies in an overlap-invariant component when
the fixed residual acts innerly on it. -/
theorem source_nonnormal_oddNormalizer_fullModule_le_component_of_overlap_normalizes
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
    (K : Subgroup (normalizer (B : Set G)))
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hYK : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (K : Set (normalizer (B : Set G))))
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) :
    D.fullModule ≤ K.map (normalizer (B : Set G)).subtype := by
  let N := normalizer (B : Set G)
  let C := localOrbit T L ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  let Y := D.maximalLocal.subgroupOf N
  let J := K.map N.subtype
  let A := Y.map N.subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ N)
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hi : F ≤ J ⊔ centralizer (J : Set G) := by
    have hh := map_mono (f := N.subtype) hinner
    rw [map_subgroupOf_eq_of_le hFN,Subgroup.map_sup] at hh
    exact hh.trans (sup_le_sup le_rfl (map_centralizer_le_centralizer_image _ _))
  obtain ⟨_,_,hVF⟩ := source_fullModule_oddActor_cover D B hBC hodd hBV
  have hV : IsPGroup 2 D.fullModule := (isPGroup_pCoreIn 2 F).to_le hVF
  have hAJ : A ≤ normalizer (J : Set G) :=
    (map_mono hYK).trans (K.le_normalizer_map N.subtype)
  have hAV : A ≤ normalizer (D.fullModule : Set G) := by
    rw [source_fullModule_normalizer D]
    rintro x ⟨y,hy,rfl⟩
    exact hy
  obtain ⟨hIM,hIN,_,_⟩ := source_oddActor_normalizerJoin_input D B hBC hodd hBV
  have hIA : I ≤ A := by
    intro x hx
    exact ⟨⟨x,hIN hx⟩,hIM hx,rfl⟩
  exact binary_subgroup_le_of_normalized_inner_product_uniqueness J D.fullModule A I
    D.maximalLocal hV (hVF.trans ((pCoreIn_le 2 F).trans hi)) hAJ hAV hIA
    hu.2.2 houtK

/-- Actual module placement and centralizer core freeness imply oddness,
with the entire source uniqueness actor retained. -/
theorem source_nonnormal_oddNormalizer_centralizer_odd_of_module_le
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
    (J : Subgroup (normalizer (B : Set G)))
    (hYJ : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (J : Set (normalizer (B : Set G))))
    (houtJ : ¬ J.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hVJ : D.fullModule.subgroupOf (normalizer (B : Set G)) ≤ J)
    (hcore : pCore 2 (centralizer (J : Set (normalizer (B : Set G)))) = ⊥) :
    Odd (Nat.card (centralizer (J : Set (normalizer (B : Set G))))) := by
  let N := normalizer (B : Set G)
  let X := localOrbit T L
  let C := X ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  let F0 := F.subgroupOf N
  let Y := D.maximalLocal.subgroupOf N
  let Z := centralizer (J : Set N)
  let U := D.fullModule.subgroupOf N
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hVN : D.fullModule ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  have hFY : F0 ≤ Y := subgroupOf_mono N
    (((map_subtype_le _).trans inf_le_left).trans X.le_normalizer)
  have hYF : Y ≤ normalizer (F0 : Set N) := by
    have hnorm : D.maximalLocal ⊓ N ≤ normalizer (F : Set G) :=
      ((le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_centralizer B))).trans
        inf_normalizer_le_normalizer_inf).trans
          (normalizer_le_normalizer_characteristic_image C (solvableResidual C))
    intro y hy f
    exact hnorm ⟨hy,y.property⟩ (f : G)
  have hZU : Z ≤ centralizer (U : Set N) := centralizer_le hVJ
  have hZY : Z ≤ Y := by
    intro z hz
    change (z : G) ∈ D.maximalLocal
    rw [←source_fullModule_normalizer D]
    apply Subgroup.centralizer_le_normalizer _
    intro v hv
    exact congrArg Subtype.val (hZU hz ⟨v,hVN hv⟩ hv)
  have hZF : Z ≤ normalizer (F0 : Set N) := hZY.trans hYF
  have hFZ : F0 ≤ normalizer (Z : Set N) :=
    (hFY.trans hYJ).trans (normalizer_le_normalizer_centralizer J)
  have hinf : F0 ⊓ Z = ⊥ := by
    let H := localJoin T L
    have hFH : F ≤ H := ((map_subtype_le _).trans inf_le_left).trans le_sup_left
    let f : (F0 ⊓ Z : Subgroup N) →*
        centralizer (D.fullModule.subgroupOf H : Set H) := {
      toFun := fun x => ⟨⟨x.val.val,hFH x.property.1⟩,by
        intro v hv
        apply Subtype.ext
        change v.val * x.val.val = x.val.val * v.val
        exact congrArg N.subtype (hZU x.property.2 ⟨v.val,hVN hv⟩ hv)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro x y he
      exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val.val) he))
    have hP : IsPGroup 2 (F0 ⊓ Z : Subgroup N) :=
      (source_nonnormal_full_module_local_kernel_isTwoGroup D hn).of_injective f hf
    have hnorm : Z ≤ normalizer (F0 ⊓ Z : Set N) :=
      (le_inf hZF Z.le_normalizer).trans inf_normalizer_le_normalizer_inf
    have hh := le_pCoreIn_of_normalizes hP (show F0 ⊓ Z ≤ Z from inf_le_right) hnorm
    rw [pCoreIn,hcore,Subgroup.map_bot] at hh
    exact le_bot_iff.mp hh
  have hFcent : F0 ≤ centralizer (Z : Set N) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    exact le_bot_iff.mp ((le_inf
      (le_normalizer_iff_commutator_le_left.mp hZF)
      (le_normalizer_iff_commutator_le_right.mp hFZ)).trans hinf.le)
  apply Nat.not_even_iff_odd.mp
  intro heven
  let R := (T : Subgroup G).subgroupOf N
  have hRY : R ≤ Y := subgroupOf_mono N (le_normalizer_componentOrbit L T)
  obtain ⟨z,hz,hzcent⟩ := exists_involution_centralizing_normalizing_two_group
    J R T.isPGroup'.comap_subtype (hRY.trans hYJ) (even_iff_two_dvd.mp heven)
  have hzZ : z ∈ Z := by
    intro j hj
    exact mem_centralizer_singleton_iff.mp (hzcent (mem_sup_left hj))
  let Q := zpowers (z : G)
  have hpow : (z : G)^2 = 1 := by
    have hh := pow_orderOf_eq_one z
    rw [hz] at hh
    exact congrArg Subtype.val hh
  have hQ : IsPGroup 2 Q :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hpow).isPGroup 2 _
  have hQne : Q ≠ ⊥ := by
    intro hb
    have h1 : (z : G) = 1 := mem_bot.mp (hb ▸ mem_zpowers (z : G))
    have h1' : z = 1 := Subtype.ext h1
    rw [h1',orderOf_one] at hz
    omega
  have hzG : orderOf (z : G) = 2 := (Subgroup.orderOf_coe z).trans hz
  have hQnorm : normalizer (Q : Set G) = centralizer ({(z : G)} : Set G) :=
    normalizer_zpowers_eq_centralizer_of_order_two (z : G) hzG
  have hFQ : F ≤ normalizer (Q : Set G) := by
    rw [hQnorm]
    intro f hf
    apply mem_centralizer_singleton_iff.mpr
    exact (congrArg Subtype.val (hFcent
      (show (⟨f,hFN hf⟩ : N) ∈ F0 from hf) z hzZ)).symm
  have hRQ : (T : Subgroup G) ⊓ N ≤ normalizer (Q : Set G) := by
    rw [hQnorm]
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp
      (hzcent (mem_sup_right (show (⟨r,hr.2⟩ : N) ∈ R from hr.1))))
  have hQM := normalizer_le_of_unique_maximalTwoLocal hu.2.2 hQ hQne (sup_le hFQ hRQ)
  apply houtJ
  apply le_trans ?_ hQM
  rw [hQnorm]
  rintro _ ⟨j,hj,rfl⟩
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hzcent (mem_sup_left hj))))

/-- The actual uniqueness actor closes component placement and identifies
its centralizer, retaining the independent inner-action premise. -/
theorem source_nonnormal_oddNormalizer_component_closure_of_overlap_normalizes
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hYK : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (K : Set (normalizer (B : Set G))))
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) :
    K.Normal ∧
    D.fullModule.subgroupOf (normalizer (B : Set G)) ≤ K ∧
    centralizer (K : Set (normalizer (B : Set G))) =
      pPrimeCore 2 (normalizer (B : Set G)) ∧
    ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K := by
  let N := normalizer (B : Set G)
  let F := ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
  have hvG := source_nonnormal_oddNormalizer_fullModule_le_component_of_overlap_normalizes
    D B hBC hodd hBV hu K houtK hYK hinner
  have hv : D.fullModule.subgroupOf N ≤ K := by
    intro v hv
    obtain ⟨w,hw,he⟩ := hvG hv
    exact (Subtype.ext he : w = v) ▸ hw
  have houtN : ¬ N ≤ D.maximalLocal := fun he => houtK ((map_subtype_le K).trans he)
  have hIN : (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
      ((T : Subgroup G) ⊓ N) ≤ N :=
    (source_oddActor_normalizerJoin_input D B hBC hodd hBV).2.1
  have hcoreN := twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup _ N
    D.maximalLocal hu.2.2 houtN
  rw [sup_eq_right.mpr hIN] at hcoreN
  have hcore := hK.centralizer_pCore_eq_bot_of_pCore_eq_bot 2 hcoreN
  have ho := source_nonnormal_oddNormalizer_centralizer_odd_of_module_le
    D hn B hBV hu K hYK houtK hv hcore
  let := source_oddNormalizer_residual_perfect (T := T) (L := L) B
  exact ⟨hK.normal_of_odd_centralizer ho,hv,
    hK.centralizer_eq_oddCore_of_odd_centralizer ho,
    hK.perfect_actor_le_of_odd_centralizer ho F hinner⟩

end CFSG.Quasithin.Chapter10
