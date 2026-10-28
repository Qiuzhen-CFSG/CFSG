module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorFiveBorel
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.PCoreOuterSylowCover
public import Theory.GroupTheory.AutomorphismSquareOuterTwo
public import Theory.GroupTheory.PResidual.ThreeFree

/-!
# The original tensor point centralizer and ambient equalities

The full kernel on K_z/O₂(K_z) normalizes X and therefore lies in M.
Rank saturation makes it three-free. The actual M_z action has the same
image as XT, a {2,3}-group, so the kernel's two-residual fixes V. The
original local action kernel and maximal-two-local uniqueness then kill
that residual. Thus the full section-action kernel is a two-group.

The actual exchanged PSL₂(5) pair has two-group outer automorphisms, so
Sylow coverage gives G_z=K_zT. The established Borel intersection now gives
M_z=XT and places the full C_M(V) inside the original local action kernel.
It too is a two-group; equality of the full and local tensor images then
gives M=L₀T. None of these ambient conclusions is assumed.

The Source application supplies the same original point, cubic Sylow,
component quotient and exchange from its checked prime-five reduction.
Tensor recognition (including the base-image equality), the strict r bound,
point-core containment, both quiet exclusions and the distinct positive
fixed-layer output remain with the selected-module owner.
Source: Aschbacher--Smith 8.3.10(2), printed p.726, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem point_twoThree
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    IsPiGroup twoThreePrimes (CentralizerSetup.XT ⟨T,localOrbit T L,z⟩) := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  obtain ⟨a⟩ := quiet_tensor_point_quotient D hn e hbase hzV hz1 hzT
  have hc : Nat.card WreathTwoResidual.Actor = 72 := by
    change Nat.card (RegularWreathProduct _ _) = 72
    rw [RegularWreathProduct.card]
    obtain ⟨b⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    rw [Nat.card_congr b.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hq : Nat.card (d.XT ⧸ pCore 2 d.XT) = 72 :=
    (Nat.card_congr a.toEquiv).trans hc
  obtain ⟨n,hnc⟩ := (pCore_isPGroup (p := 2) (G := d.XT)).exists_card_eq
  apply (IsPiGroup_iff _ _).mpr
  intro p hp
  have hcard := (pCore 2 d.XT).card_mul_index
  rw [index_eq_card,hnc,hq] at hcard
  rw [←hcard] at hp
  rcases p.property.dvd_mul.mp hp with htwo | hsmall
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow htwo) |>.resolve_left p.property.ne_one)
  · rw [show 72 = 2^3 * 3^2 from rfl] at hsmall
    rcases p.property.dvd_mul.mp hsmall with htwo | hthree
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
        (p.property.dvd_of_dvd_pow htwo) |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp
        (p.property.dvd_of_dvd_pow hthree) |>.resolve_left p.property.ne_one)

private theorem normalizer_action_restrict
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (a : localJoin T L) :
    quietTensorNormalizerAction D e
      ⟨a,D.maximalLocal_normalizes_fullModule
        ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) a.property)⟩ =
      quietTensorLinearAction D e a := by
  apply LinearEquiv.ext
  intro w
  obtain ⟨v,rfl⟩ := e.surjective w
  rw [quietTensorNormalizerAction_apply,quietTensorLinearAction_apply]

/-- A three-free two-perfect subgroup of the original M_z fixes the full tensor module. -/
theorem quiet_tensor_three_free_point_residual_centralizes
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (Y : Subgroup G) (hYM : Y ≤ D.maximalLocal)
    (hYz : Y ≤ centralizer ({z} : Set G))
    (hp : IsPPerfect 2 Y) (hthree : ¬ 3 ∣ Nat.card Y) :
    Y ≤ centralizer (D.fullModule : Set G) := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let N := normalizer (D.fullModule : Set G)
  let f := (quietTensorNormalizerAction D e).comp
    (inclusion (hYM.trans D.maximalLocal_normalizes_fullModule))
  have hXT : d.XT = localJoin T L ⊓ d.Gz := quiet_XT_eq_point_centralizer hzT
  let g := (quietTensorLinearAction D e).comp (inclusion (hXT.le.trans inf_le_left))
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let : Finite g.range := Finite.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hfg : f.range ≤ g.range := by
    rintro _ ⟨y,rfl⟩
    have hy : f y ∈ (quietTensorLinearAction D e).range := by
      rw [quiet_tensor_action_image_of_orbit_image D hn e hbase,
        ←quiet_tensor_normalizer_image D hn e hbase]
      exact ⟨inclusion (hYM.trans D.maximalLocal_normalizes_fullModule) y,rfl⟩
    obtain ⟨a,ha⟩ := hy
    have hay : quietTensorLinearAction D e a (e (Additive.ofMul ⟨z,hzV⟩)) =
        e (Additive.ofMul ⟨z,hzV⟩) := by
      rw [ha]
      change quietTensorNormalizerAction D e _ _ = _
      rw [quietTensorNormalizerAction_apply]
      congr 1
      apply congrArg Additive.ofMul
      apply Subtype.ext
      change (y : G)*z*(y : G)⁻¹ = z
      rw [mem_centralizer_singleton_iff.mp (hYz y.property),mul_inv_cancel_right]
    rw [quietTensorLinearAction_apply] at hay
    have haz := congrArg (fun v : Additive D.fullModule => (v.toMul : G)) (e.injective hay)
    change (a : G)*z*(a : G)⁻¹ = z at haz
    have haz' : (a : G) ∈ d.Gz :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp haz)
    exact ⟨⟨a,hXT.ge ⟨a.property,haz'⟩⟩,ha⟩
  have h23 : IsPiGroup twoThreePrimes f.range :=
    ((point_twoThree D hn e hbase hzV hz1 hzT).of_surjective
      g.rangeRestrict g.rangeRestrict_surjective).of_injective
        (inclusion hfg) (inclusion_injective hfg)
  have hp2 : IsPGroup 2 f.range := isPGroup_two_of_isPiGroup_twoThree h23
    (fun hd => hthree (hd.trans (card_dvd_of_surjective
      f.rangeRestrict f.rangeRestrict_surjective)))
  have hf := hp.hom_eq_one_of_isPGroup hp2 f.rangeRestrict
  intro y hy v hv
  have he : f ⟨y,hy⟩ = 1 := congrArg Subtype.val (show f.rangeRestrict ⟨y,hy⟩ = 1 from DFunLike.congr_fun hf ⟨y,hy⟩)
  have hh := LinearEquiv.congr_fun he (e (Additive.ofMul ⟨v,hv⟩))
  change quietTensorNormalizerAction D e _ _ = _ at hh
  rw [quietTensorNormalizerAction_apply] at hh
  have hc := congrArg (fun w : Additive D.fullModule => (w.toMul : G)) (e.injective hh)
  change y*v*y⁻¹ = v at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

/-- The complete section-action kernel is contained in the original point normalizer. -/
theorem quiet_tensor_point_action_kernel_le
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let f := (pCoreNormalizerAction 2 d.Kz).comp
      (inclusion (le_normalizer_conjugateSpanBy d.X d.Gz))
    f.ker.map d.Gz.subtype ≤ D.maximalLocal := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let f := (pCoreNormalizerAction 2 d.Kz).comp
    (inclusion (le_normalizer_conjugateSpanBy d.X d.Gz))
  let B := f.ker.map d.Gz.subtype
  have hi := quiet_tensor_point_localInput D hn e hbase hzV hz1 hzT P
  have hKn : d.Gz ≤ normalizer (d.Kz : Set G) := le_normalizer_conjugateSpanBy _ _
  have hcoreH : d.Gz.pCoreIn 2 ≤ normalizer (d.X : Set G) := by
    rw [←hi.residual]
    exact le_sup_left.trans (le_normalizer_embedded_pResidual 2 _)
  have hcore : d.Kz.pCoreIn 2 ≤ normalizer (d.X : Set G) :=
    (pCoreIn_mono_of_normalizes d.Kz_le_Gz hKn).trans hcoreH
  have hBN : B ≤ normalizer (d.X : Set G) := by
    rintro g ⟨x,hx,rfl⟩
    apply mem_normalizer_of_pCoreNormalizerAction_preserves_image d.Kz d.X d.X_le_Kz
      hi.perfect hcore (inclusion hKn x)
    change pCoreNormalizerAction 2 d.Kz (inclusion hKn x) = 1 at hx
    rw [hx]
    exact map_id _
  exact (le_inf (map_subtype_le _) hBN).trans
    (quiet_tensor_point_normalizer_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT)

/-- Rank saturation rules out cubic elements in the full action kernel. -/
theorem quiet_tensor_point_action_kernel_three_free
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let f := (pCoreNormalizerAction 2 d.Kz).comp
      (inclusion (le_normalizer_conjugateSpanBy d.X d.Gz))
    ¬ 3 ∣ Nat.card (f.ker.map d.Gz.subtype) := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let f := (pCoreNormalizerAction 2 d.Kz).comp
    (inclusion (le_normalizer_conjugateSpanBy d.X d.Gz))
  let B := f.ker.map d.Gz.subtype
  let P₀ := (P : Subgroup d.X).map d.X.subtype
  have hi := quiet_tensor_point_localInput D hn e hbase hzV hz1 hzT P
  obtain ⟨K,hq,⟨c⟩,p,hp,ho,F,_,_,hF,⟨a⟩⟩ :=
    quiet_tensor_point_odd_square D hmany hmin hn hJ cL e hbase hzV hz1 hzT P
  have hzK : center (XiQuotient K) = ⊥ :=
    (Theory.PSL2.primeField_center_outer_of_equiv hp ho hF a).1
  have hz : center (XiQuotient d.Kz) = ⊥ := by
    apply bot_unique
    intro x hx
    have hh : c x ∈ center (XiQuotient K × XiQuotient K) :=
      (centerCongr c ⟨x,hx⟩).property
    rw [Subgroup.center_prod,hzK,bot_prod_bot,mem_bot] at hh
    exact c.map_eq_one_iff.mp hh
  have hrP : 2 ≤ primeRank 3 P₀ := by
    by_contra hh
    have hr1 : primeRank 3 P₀ ≤ 1 := by omega
    apply hi.odd_complement.not_isCyclic
    apply hi.odd_complement.isPGroup.isCyclic_of_odd_of_elementary_card_le (by decide)
    intro E hE
    let := hE
    exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr1 E
  have hrK : 2 ≤ primeRank 3 d.Kz := hrP.trans
    (primeRank_mono 3 (hi.complement_le.trans d.X_le_Kz))
  have hBG : B ≤ d.Gz := map_subtype_le _
  have hBN : B ≤ normalizer (d.Kz : Set G) :=
    hBG.trans (le_normalizer_conjugateSpanBy _ _)
  have hcomm : ⁅B,d.Kz⁆ ≤ d.Kz.pCoreIn 2 := by
    rw [commutator_comm]
    apply commutator_le_core_of_pCoreNormalizerAction_eq_one 2 d.Kz B hBN
    rintro ⟨_,x,hx,rfl⟩
    exact hx
  have hr := ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
    (by decide : Odd 3) B d.Kz hBN
    ((commutator_mono (map_subtype_le _) le_rfl).trans hcomm)
    (by rw [hz,card_bot]; exact Nat.coprime_one_right 3)
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hu := (primeRank_mono 3 (sup_le hBG d.Kz_le_Gz)).trans
    (D.simpleQTKE.involution_centralizer_stronglyQuasithin hz2 3 (by decide) (by decide))
  exact PrimeRank.eq_zero_iff_not_dvd_card.mp (show primeRank 3 B = 0 from by omega)

/-- A normal three-free subgroup of the original point centralizer lying in M
is a two-group. Its two-residual is killed using the original module kernel
and maximal-two-local uniqueness, with normality only inside G_z. -/
theorem quiet_tensor_normal_point_three_free_isTwoGroup
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (C : Subgroup G) (hCM : C ≤ D.maximalLocal)
    (hCz : C ≤ centralizer ({z} : Set G))
    (hGC : centralizer ({z} : Set G) ≤ normalizer (C : Set G))
    (hthree : ¬ 3 ∣ Nat.card C) : IsPGroup 2 C := by
  let H := centralizer ({z} : Set G)
  let R := localOrbit T L
  let Q := R.pCoreIn 2
  let Y := (pResidual 2 C).map C.subtype
  have hYC : Y ≤ C := map_subtype_le _
  have hHY : H ≤ normalizer (Y : Set G) := hGC.trans
    (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))
  have hYV := quiet_tensor_three_free_point_residual_centralizes D hn e hbase hzV hz1 hzT
    Y (hYC.trans hCM) (hYC.trans hCz) (isPPerfect_embedded_pResidual 2 C)
    (fun hd => hthree (hd.trans (card_dvd_of_le hYC)))
  have hQn : R ≤ normalizer (Q : Set G) := R.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image R (pCore 2 R))
  have hkernel : R ⊓ centralizer (D.fullModule : Set G) ≤ Q := by
    let B := R ⊓ centralizer (D.fullModule : Set G)
    have hBH : B ≤ localJoin T L := inf_le_left.trans le_sup_left
    let j : B →* centralizer
        (D.fullModule.subgroupOf (localJoin T L) : Set (localJoin T L)) :=
      { toFun := fun b => ⟨⟨b,hBH b.property⟩,fun v hv =>
          Subtype.ext (b.property.2 v hv)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := fun x y hh =>
      Subtype.ext (congrArg (fun a : centralizer
        (D.fullModule.subgroupOf (localJoin T L) : Set (localJoin T L)) => a.val.val) hh)
    have hB2 := (full_module_local_kernel_isTwoGroup D hn).of_injective j hj
    apply le_pCoreIn_of_normalizes hB2 inf_le_left
    exact (le_inf R.le_normalizer
      (((localOrbit T L).le_normalizer.trans D.maximalLocal_normalizes_fullModule).trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  have hcomm : ⁅R,Y⁆ ≤ Q := by
    apply (le_inf ?_ ?_).trans hkernel
    · exact le_normalizer_iff_commutator_le_left.mp (hYC.trans hCM)
    · exact (commutator_mono le_rfl hYV).trans
        (le_normalizer_iff_commutator_le_right.mp
          (((localOrbit T L).le_normalizer.trans D.maximalLocal_normalizes_fullModule).trans (normalizer_le_normalizer_centralizer _)))
  have hQH : Q ≤ H := by
    have hQN : Q ≤ (localJoin T L).pCoreIn 2 :=
      pCoreIn_mono_of_normalizes le_sup_left
        (sup_le R.le_normalizer (le_normalizer_componentOrbit L T))
    have hQT := pCoreIn_le_sylow (localJoin T L) (T.subtype le_sup_right)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] at hQT
    exact hQN.trans (hQT.trans hzT)
  have hRY : R ≤ normalizer (Y : Set G) :=
    normalizes_residual_of_commutator_le_two R H C Q hGC hQH
      (isPGroup_pCoreIn 2 R) hQn hcomm
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hchar := mem_He_iff.mp (twoLocal_mem_He_of_sylow_le T
    (D.simpleQTKE.evenCharacteristic T) (isTwoLocal_involution_centralizer hz2) hzT)
  have hself : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2 := by
    rintro x ⟨hx,hc⟩
    exact mem_map_of_mem H.subtype (hchar (show (⟨x,hx⟩ : H) ∈
      centralizer (pCore 2 H : Set H) from fun q hq =>
        Subtype.ext (hc q (mem_map_of_mem H.subtype hq))))
  have hY : Y = ⊥ := normal_eq_bot_of_unique_core (localJoin T L) H D.maximalLocal Y
    (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.2
    (quiet_point_centralizer_not_le D hmany hJ hzV hzT) hself
    (hYC.trans hCz) hHY (sup_le hRY (hzT.trans hHY))
  have hr : pResidual 2 C = ⊥ := (map_eq_bot_iff_of_injective _ C.subtype_injective).mp hY
  exact (isPGroup_quotient_pResidual (G := C) 2).of_injective
    (QuotientGroup.mk' (pResidual 2 C)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk',hr])

/-- The full action kernel, including all ambient centralizing elements, is a two-group. -/
theorem quiet_tensor_point_action_kernel_isTwoGroup
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let f := (pCoreNormalizerAction 2 d.Kz).comp
      (inclusion (le_normalizer_conjugateSpanBy d.X d.Gz))
    IsPGroup 2 f.ker := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let f := (pCoreNormalizerAction 2 d.Kz).comp
    (inclusion (le_normalizer_conjugateSpanBy d.X d.Gz))
  have hnormal : d.Gz ≤ normalizer (f.ker.map d.Gz.subtype : Set G) := by
    have hh := f.ker.le_normalizer_map d.Gz.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hp := quiet_tensor_normal_point_three_free_isTwoGroup D hmany hn hJ e hbase hzV hz1 hzT
    (f.ker.map d.Gz.subtype)
    (quiet_tensor_point_action_kernel_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT P)
    (map_subtype_le _) hnormal
    (quiet_tensor_point_action_kernel_three_free D hmany hmin hn hJ cL e hbase hzV hz1 hzT P)
  exact hp.of_equiv (f.ker.equivMapOfInjective d.Gz.subtype d.Gz.subtype_injective).symm

/-- Source 8.3.10(2): the original point centralizer is exactly K_z T. -/
theorem quiet_tensor_point_centralizer_eq
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    {K : Subgroup G}
    (hs : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) d.X
        ((P : Subgroup d.X).map d.X.subtype) d.Gz K)
    (hclosure : CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩ = componentOrbit K (T : Subgroup G))
    (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 5) :
    CentralizerSetup.Gz ⟨T,localOrbit T L,z⟩ = CentralizerSetup.KzT ⟨T,localOrbit T L,z⟩ := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  obtain ⟨c⟩ := swapped_product hs
  have hq : IsQuasisimple (XiQuotient K) := hs.quasisimple
  let := hq
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
  obtain ⟨hz,ho⟩ := Theory.PSL2.primeField_center_outer_of_equiv
    (by decide : Nat.Prime 5) (by decide : Odd 5) hF a
  have houter : IsPGroup 2 (MulAut.Outer (XiQuotient d.Kz)) := by
    rw [hclosure]
    exact (AutomorphismSquare.outer_isPGroup_two hz ho).of_surjective
      (MulAut.outerCongr c.symm).toMonoidHom (MulAut.outerCongr c.symm).surjective
  have hh := subgroup_sup_sylow_eq_top_of_twoCore_action_kernel d.Gz d.Kz d.Kz_le_Gz
    (le_normalizer_conjugateSpanBy d.X d.Gz) (T.subtype hzT) houter
    (quiet_tensor_point_action_kernel_isTwoGroup D hmany hmin hn hJ cL e hbase hzV hz1 hzT P)
  have hm := congrArg (map d.Gz.subtype) hh
  change ((d.Kz.subgroupOf d.Gz) ⊔ (T : Subgroup G).subgroupOf d.Gz).map d.Gz.subtype =
    (⊤ : Subgroup d.Gz).map d.Gz.subtype at hm
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le d.Kz_le_Gz,
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ d.Gz from hzT),
    ←MonoidHom.range_eq_map,range_subtype] at hm
  exact hm.symm

/-- The ambient equalities of 8.3.10(2), with the full M-action kernel retained. -/
theorem quiet_tensor_five_ambient_equalities
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    {K : Subgroup G}
    (hs : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) d.X
        ((P : Subgroup d.X).map d.X.subtype) d.Gz K)
    (hclosure : CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩ = componentOrbit K (T : Subgroup G))
    (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 5) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    d.Gz = d.KzT ∧ d.Mz = d.XT ∧
      IsPGroup 2 (centralizer (D.fullModule.subgroupOf D.maximalLocal : Set D.maximalLocal)) ∧
      D.maximalLocal = localJoin T L := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hpoint := quiet_tensor_point_centralizer_eq D hmany hmin hn hJ cL e hbase
    hzV hz1 hzT P hs hclosure hm
  have hinter := (quiet_tensor_five_borel_hstar D hmany hmin hn hJ cL e hbase
    hzV hz1 hzT P hs hclosure hm).2.2.2
  have hMz : d.Mz = d.XT := by
    change D.maximalLocal ⊓ d.Gz = d.XT
    rw [hpoint,inf_comm]
    exact hinter
  let H := localJoin T L
  let M := D.maximalLocal
  let C := centralizer (D.fullModule.subgroupOf M : Set M)
  have hHM : H ≤ M :=
    sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
  have hVM : D.fullModule ≤ M :=
    (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)).trans
      (le_normalizer_componentOrbit L T)
  have hCH : C.map M.subtype ≤ H := by
    rintro _ ⟨c,hc,rfl⟩
    have hcz : (c : G) ∈ d.Gz := by
      apply mem_centralizer_singleton_iff.mpr
      exact (congrArg M.subtype (hc ⟨z,hVM hzV⟩ hzV)).symm
    have hXT : (c : G) ∈ d.XT := hMz ▸ (show (c : G) ∈ d.Mz from ⟨c.property,hcz⟩)
    exact ((quiet_XT_eq_point_centralizer (T := T) (L := L) hzT).le hXT).1
  let j : C →* centralizer (D.fullModule.subgroupOf H : Set H) :=
    { toFun := fun c => ⟨⟨c.val,hCH (mem_map_of_mem M.subtype c.property)⟩,fun v hv =>
        Subtype.ext (congrArg M.subtype (c.property ⟨v,hHM v.property⟩ hv))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : centralizer (D.fullModule.subgroupOf H : Set H) => a.val.val) hh
  have hp : IsPGroup 2 C := (full_module_local_kernel_isTwoGroup D hn).of_injective j hj
  let : (D.fullModule.subgroupOf M).Normal := (source_full_module_reduced D).normal
  have hCT : C ≤ (T : Subgroup G).subgroupOf M :=
    hp.le_sylow_of_normal (T.subtype (le_normalizer_componentOrbit L T))
  refine ⟨hpoint,hMz,hp,le_antisymm ?_ hHM⟩
  intro m hm
  let mN : normalizer (D.fullModule : Set G) := ⟨m,D.maximalLocal_normalizes_fullModule hm⟩
  have hma : quietTensorNormalizerAction D e mN ∈ (quietTensorLinearAction D e).range := by
    rw [quiet_tensor_action_image_of_orbit_image D hn e hbase,
      ←quiet_tensor_normalizer_image D hn e hbase]
    exact ⟨mN,rfl⟩
  obtain ⟨a,ha⟩ := hma
  let aN : normalizer (D.fullModule : Set G) :=
    ⟨a,D.maximalLocal_normalizes_fullModule (hHM a.property)⟩
  have he : quietTensorNormalizerAction D e (mN*aN⁻¹) = 1 := by
    rw [map_mul,map_inv,normalizer_action_restrict D e a,ha,mul_inv_cancel]
  have hc : (⟨m*(a : G)⁻¹,M.mul_mem hm (M.inv_mem (hHM a.property))⟩ : M) ∈ C := by
    intro v hv
    have hh := LinearEquiv.congr_fun he (e (Additive.ofMul ⟨v,hv⟩))
    rw [quietTensorNormalizerAction_apply] at hh
    have hg := congrArg (fun w : Additive D.fullModule => (w.toMul : G)) (e.injective hh)
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul.mp hg).symm
  have hmH : m*(a : G)⁻¹ ∈ H := (show (T : Subgroup G) ≤ H from le_sup_right) (hCT hc)
  have hx := H.mul_mem hmH a.property
  simpa only [inv_mul_cancel_right] using hx


end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
