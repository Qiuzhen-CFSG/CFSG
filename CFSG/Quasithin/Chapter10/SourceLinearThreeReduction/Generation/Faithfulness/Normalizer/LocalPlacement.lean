module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalNormality
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.Placement


/-!
# Placing the fixed residual using a local moved module

The original covering subgroup normalizes the local module and a normal
escaping component. Inner projection and covering uniqueness place that
module in the component. The original pair-action kernel is a two-group;
this kills the intersection of the fixed residual with the component
centralizer. An even centralizer would supply a fixed involution and force
the component into M, so the centralizer is the odd core and the entire
perfect residual lies in the component.

Only the displayed local module is fixed by the odd actor. Soluble outer
action supplies one proved route to the explicit inner-action premise.
Source: Aschbacher--Smith 4.4.10--11, printed pp.621--622, as used in
10.2.3(2), p.745 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Actual module placement and centralizer core freeness imply oddness,
with the entire source uniqueness actor retained. -/
private theorem centralizer_odd_of_module_le
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (W : Subgroup G) (hWV : W ≤ D.fullModule) (hne : W ≠ ⊥)
    (hWX : W = ⁅W,localOrbit T L⁆)
    (hNW : localJoin T L ≤ normalizer (W : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (B : Subgroup G) (hB : IsPGroup p B)
    (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (W : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
    (J : Subgroup (normalizer (B : Set G)))
    (hYJ : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (J : Set (normalizer (B : Set G))))
    (houtJ : ¬ J.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hVJ : W.subgroupOf (normalizer (B : Set G)) ≤ J)
    (hcore : pCore 2 (centralizer (J : Set (normalizer (B : Set G)))) = ⊥) :
    Odd (Nat.card (centralizer (J : Set (normalizer (B : Set G))))) := by
  let N := normalizer (B : Set G)
  let X := localOrbit T L
  let C := X ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  let F0 := F.subgroupOf N
  let Y := D.maximalLocal.subgroupOf N
  let Z := centralizer (J : Set N)
  let U := W.subgroupOf N
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hVN : W ≤ N := (le_centralizer_iff.mp hBV).trans
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
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  have hZU : Z ≤ centralizer (U : Set N) := centralizer_le hVJ
  have hZY : Z ≤ Y := by
    intro z hz
    change (z : G) ∈ D.maximalLocal
    apply normalizer_le_of_unique_maximalTwoLocal
      (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.2
      ((IsElementaryAbelian.isPGroup 2 D.fullModule).to_le hWV) hne hNW
    apply Subgroup.centralizer_le_normalizer _
    intro v hv
    exact congrArg Subtype.val (hZU hz ⟨v,hVN hv⟩ hv)
  have hZF : Z ≤ normalizer (F0 : Set N) := hZY.trans hYF
  have hFZ : F0 ≤ normalizer (Z : Set N) :=
    (hFY.trans hYJ).trans (normalizer_le_normalizer_centralizer J)
  have hinf : F0 ⊓ Z = ⊥ := by
    let I := F ⊔ ((T : Subgroup G) ⊓ N)
    have hIW : I ≤ normalizer (W : Set G) := (sup_le
      (((map_subtype_le _).trans inf_le_left).trans (show X ≤ localJoin T L from le_sup_left))
      (inf_le_left.trans (show (T : Subgroup G) ≤ localJoin T L from le_sup_right))).trans hNW
    let a : I →* MulAut W := W.normalizerMonoidHom.comp (inclusion hIW)
    let g := a.comp (inclusion (show F ≤ I from le_sup_left))
    have ho : Odd (Nat.card B) := by
      obtain ⟨n,he⟩ := hB.exists_card_eq
      rw [he]
      exact hp.pow
    have hmove := (source_local_oddActor_cover D W hWV hWX hNW B hBC ho hBV).2.1
    have hg : g ≠ 1 := by
      intro hz
      have hFW : F ≤ centralizer (W : Set G) := by
        intro x hx w hw
        have hh := DFunLike.congr_fun hz (⟨x,hx⟩ : F)
        have hv := congrArg (fun b : MulAut W => (b ⟨w,hw⟩ : G)) hh
        change x*w*x⁻¹ = w at hv
        exact (mul_inv_eq_iff_eq_mul.mp hv).symm
      exact hne (hmove.trans (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp hFW)))
    have hk : IsPGroup 2 g.ker :=
      source_nonnormal_oddActorResidual_hom_kernel D hn hp B hB hBC hperm a hg
    let f : (F0 ⊓ Z : Subgroup N) →* g.ker := {
      toFun := fun x => ⟨⟨x.val.val,x.property.1⟩,by
        apply MulEquiv.ext
        intro w
        apply Subtype.ext
        change x.val.val * w.val * x.val.val⁻¹ = w.val
        have hc := congrArg Subtype.val (hZU x.property.2 ⟨w.val,hVN w.property⟩ w.property)
        exact mul_inv_eq_iff_eq_mul.mpr hc.symm⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro x y he
      exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val.val) he))
    have hP : IsPGroup 2 (F0 ⊓ Z : Subgroup N) := hk.of_injective f hf
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

/-- Inner action on a normal escaping component places the local module and the entire fixed residual in it. -/
theorem source_local_oddPrimeActor_component_closure
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (W : Subgroup G) (hWV : W ≤ D.fullModule) (hne : W ≠ ⊥)
    (hWX : W = ⁅W,localOrbit T L⁆)
    (hNW : localJoin T L ≤ normalizer (W : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (B : Subgroup G) (hB : IsPGroup p B)
    (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (W : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) :
    W.subgroupOf (normalizer (B : Set G)) ≤ K ∧
    centralizer (K : Set (normalizer (B : Set G))) =
      pPrimeCore 2 (normalizer (B : Set G)) ∧
    ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K := by
  let N := normalizer (B : Set G)
  let C := localOrbit T L ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ N)
  let J := K.map N.subtype
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hIN : I ≤ N := sup_le hFN inf_le_right
  have hIW : I ≤ normalizer (W : Set G) := (sup_le
    (((map_subtype_le _).trans inf_le_left).trans (show localOrbit T L ≤ localJoin T L from le_sup_left))
    (inf_le_left.trans (show (T : Subgroup G) ≤ localJoin T L from le_sup_right))).trans hNW
  have hNJ : N ≤ normalizer (J : Set G) := by
    have hh := K.le_normalizer_map N.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hi : F ≤ J ⊔ centralizer (J : Set G) := by
    have hh := map_mono (f := N.subtype) hinner
    rw [map_subgroupOf_eq_of_le hFN,Subgroup.map_sup] at hh
    exact hh.trans (sup_le_sup le_rfl (map_centralizer_le_centralizer_image _ _))
  have ho : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  obtain ⟨_,_,hWF⟩ := source_local_oddActor_cover D W hWV hWX hNW B hBC ho hBV
  have hu := source_local_oddPrimeActor_covering_uniqueness D hn W hWV hne hWX hNW
    hp B hB hBC hBV hperm
  have hWJ : W ≤ J := binary_subgroup_le_of_normalized_inner_product_uniqueness
    J W I I D.maximalLocal ((isPGroup_pCoreIn 2 F).to_le hWF)
    (hWF.trans ((pCoreIn_le 2 F).trans hi)) (hIN.trans hNJ) hIW le_rfl hu.2.2 hout
  have hWK : W.subgroupOf N ≤ K := by
    intro w hw
    obtain ⟨v,hv,he⟩ := hWJ hw
    exact (Subtype.ext he : v = w) ▸ hv
  have hcoreN : pCore 2 N = ⊥ := by
    by_contra hc
    exact hout ((map_subtype_le K).trans
      (source_local_oddPrimeActor_normalizer_of_twoCore D hn W hWV hne hWX hNW
        hp B hB hBC hBV hperm hc))
  have hY : D.maximalLocal.subgroupOf N ≤ normalizer (K : Set N) :=
    le_trans le_top le_normalizer_of_normal
  have hodd := centralizer_odd_of_module_le D hn W hWV hne hWX hNW hp B hB hBC hBV
    hperm hu K hY hout hWK (hK.centralizer_pCore_eq_bot_of_pCore_eq_bot 2 hcoreN)
  let := source_oddNormalizer_residual_perfect (T := T) (L := L) B
  exact ⟨hWK,hK.centralizer_eq_oddCore_of_odd_centralizer hodd,
    hK.perfect_actor_le_of_odd_centralizer hodd (F.subgroupOf N) hinner⟩

/-- Soluble outer action discharges the inner-action premise for the local module. -/
theorem source_local_oddPrimeActor_residual_le_of_solvable_outer
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (W : Subgroup G) (hWV : W ≤ D.fullModule) (hne : W ≠ ⊥)
    (hWX : W = ⁅W,localOrbit T L⁆)
    (hNW : localJoin T L ≤ normalizer (W : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (B : Subgroup G) (hB : IsPGroup p B)
    (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (W : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    [Group.IsSolvable (MulAut.Outer K)]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal) :
    ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K := by
  exact (source_local_oddPrimeActor_component_closure D hn W hWV hne hWX hNW
    hp B hB hBC hBV hperm K hK hout
    (source_oddNormalizer_component_inner B K hK (le_trans le_top le_normalizer_of_normal))).2.2

end CFSG.Quasithin.Chapter10
