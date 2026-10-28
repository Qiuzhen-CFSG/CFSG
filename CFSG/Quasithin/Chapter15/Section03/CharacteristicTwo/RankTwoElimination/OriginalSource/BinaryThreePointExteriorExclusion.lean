module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointExteriorSeed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCubicPlane
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCubicSupport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeAmbientSourceNormalizer
public import Theory.Representation.BinaryEndpointInduction.EndpointCubicRank
public import Theory.Representation.BinaryParabolicExteriorSquare.SingularCubicObstruction
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Excluding the actual exterior-six branch of the original point span

The original commuting cubic pair survives injectively in the same point
quotient and lies in the actual containing component. The first cubic
moves a point of the opposed intrinsic four, while the second fixes that
four. The displaced vector remains in the original core center and is
therefore singular under the same whole-module coordinates. The checked
singular cubic obstruction forces it to vanish, contradicting movement.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix Representation
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open BinaryEndpointInduction
open Representation.BinaryParabolicExteriorSquare.SingularCubicObstruction
variable {G : Type*} [Group G] [Finite G]

/-- A whole exterior-six realization is impossible for the original point,
component and opposed-four cubic pair. -/
theorem binary_three_source_exterior_model_impossible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2)
    (hz : z ∈ intrinsicFour c.L) (hz1 : z≠1)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S)
    [hW : IsElementaryAbelian 2
      (conjugateSpanBy ⁅coreCenter c.L,c.L⁆ (centralizer ({z} : Set G)))]
    (σ : let := hW; Representation (ZMod 2)
      (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G)))
      (Additive (conjugateSpanBy ⁅coreCenter c.L,c.L⁆ (centralizer ({z} : Set G)))))
    (hσ : ∀ (x : centralizer ({z} : Set G))
      (w : Additive (conjugateSpanBy ⁅coreCenter c.L,c.L⁆ (centralizer ({z} : Set G)))),
      ((σ (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) x) w).toMul:G)=
        x*(w.toMul:G)*(x:G)⁻¹)
    (eK : K ≃* SL(4,ZMod 2))
    (heK : (((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))).subgroupOf K).map
      eK.toMonoidHom=endpointParabolic)
    (E : let := hW; Additive
      (conjugateSpanBy ⁅coreCenter c.L,c.L⁆ (centralizer ({z} : Set G))) ≃ₗ[ZMod 2]
      (Fin 6 → ZMod 2))
    (hE : ∀ (k : K)
      (w : Additive (conjugateSpanBy ⁅coreCenter c.L,c.L⁆ (centralizer ({z} : Set G)))),
      E (σ k.val w)=E w ᵥ* survivorModelMatrix false ((eK k)⁻¹)) : False
 := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  let U := (intrinsicFour c.L).conjBy g
  let := hW
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hYL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  obtain ⟨a,v,u,haY,hvL,ha,hv,haz,hvz,hav,hvY,haU,hvU,hUV,huU,hmove⟩ :=
    binary_three_source_cubics_move_opposed_plane
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hz g hgT hgS
  obtain ⟨D,hDC,haD,hvD,hD,hDcard⟩ :=
    elementary_nine_of_commuting_cubics (YL d c.L) z a v haY hvY ha hv haz hvz hav
  let := hD
  let D₀ := D.subgroupOf C
  have hD₀ : IsPGroup 3 D₀ :=
    (IsElementaryAbelian.isPGroup 3 D).of_equiv (subgroupOfEquivOfLe hDC).symm
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    obtain ⟨n,hn⟩ := hq.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hi := injective_comp_subtype_of_coprime_ker q hcop D₀ hD₀
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hr := binary_three_source_point_quotient_normalizer_rank
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz hz1 hLS P hP g hgT hgS
  obtain ⟨eB⟩ := (point_centralizer_quotient_local d c.L e b z hLS P hP).2
  let : IsSimpleGroup (PSL(4,ZMod 2)) := Atlas.psl_simple_high_rank 4 (by decide)
  let : IsSimpleGroup SL(4,ZMod 2) :=
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0<4)).symm.isSimpleGroup
  let : IsSimpleGroup K := eK.isSimpleGroup
  have hDK : D₀.map q ≤ K := binary_three_three_subgroup_le_finite_containing
    hBK eB hr (Or.inr (Or.inl ⟨4,Or.inl rfl,hm⟩)) (hD₀.map q)
  let f : D₀ →* K := {
    toFun x := ⟨q x,hDK (mem_map_of_mem q x.property)⟩
    map_one' := Subtype.ext q.map_one
    map_mul' x y := Subtype.ext (q.map_mul x y) }
  have hf : Function.Injective f := fun x y hh => hi (congrArg Subtype.val hh)
  let π := eK.toMonoidHom.comp f
  have hπ : Function.Injective π := eK.injective.comp hf
  let aa : D₀ := ⟨⟨a,haz⟩,haD⟩
  let vv : D₀ := ⟨⟨v,hvz⟩,hvD⟩
  have ha3 : orderOf (π aa)=3 := (orderOf_injective π hπ aa).trans
    ((Subgroup.orderOf_coe aa).symm.trans ((Subgroup.orderOf_coe (aa:C)).symm.trans ha))
  have hv3 : orderOf (π vv)=3 := (orderOf_injective π hπ vv).trans
    ((Subgroup.orderOf_coe vv).symm.trans ((Subgroup.orderOf_coe (vv:C)).symm.trans hv))
  have hv0 : π vv≠1 := by intro hh; rw [hh,orderOf_one] at hv3; omega
  have hva : π vv≠π aa := by
    intro hh
    have he : v=a := congrArg (fun x : D₀ => ((x:C):G)) (hπ hh)
    exact hvY (he ▸ haY)
  have hva2 : π vv≠(π aa)^2 := by
    intro hh
    have he : v=a^2 := congrArg (fun x : D₀ => ((x:C):G))
      (hπ (hh.trans (π.map_pow aa 2).symm))
    exact hvY (he ▸ (YL d c.L).pow_mem haY 2)
  have hcomm : Commute (π aa) (π vv) := by
    exact (show Commute aa vv from Subtype.ext (Subtype.ext hav)).map π
  have haP : π aa ∈ endpointParabolic := by
    rw [←heK]
    exact mem_map_of_mem eK.toMonoidHom
      (show f aa ∈ B.subgroupOf K from mem_map_of_mem q (hYL haY))
  have haPow : (π aa)^3=1 := by simpa only [ha3] using pow_orderOf_eq_one (π aa)
  have hvPow : (π vv)^3=1 := by simpa only [hv3] using pow_orderOf_eq_one (π vv)
  have ha0 : π aa≠1 := by intro hh; rw [hh,orderOf_one] at ha3; omega
  have hrank := endpoint_cubic_fixed_finrank (π aa) haP haPow ha0
  have hVW : V ≤ W := le_conjugateSpanBy V C
  let w : Additive W := Additive.ofMul ⟨u,hVW (hUV huU)⟩
  let y : Additive W := σ (f aa).val w-w
  have hyVal : (y.toMul:G)=a*u*a⁻¹/u := by
    change ((σ (f aa).val w-w).toMul:G)=_
    rw [_root_.toMul_sub,Subgroup.coe_div]
    change ((σ (q ⟨a,haz⟩) w).toMul:G)/u=_
    rw [hσ]
    rfl
  have hy0 : y≠0 := by
    intro hh
    have he := congrArg (fun x : Additive W => (x.toMul:G)) hh
    rw [hyVal] at he
    exact hmove (div_eq_one.mp he)
  have hyU : (y.toMul:G) ∈ U := by
    rw [hyVal]
    exact U.div_mem ((mem_normalizer_iff.mp haU u).mp huU) huU
  have hLZ : c.L ≤ normalizer (coreCenter c.L) :=
    (normalizer_commutator_ge_right _ _).trans
      (normalizer_le_normalizer_characteristic_image (LinearThree.commutatorCore c.L)
        (center (LinearThree.commutatorCore c.L)))
  have hVZ : V ≤ coreCenter c.L := le_normalizer_iff_commutator_le_left.mp hLZ
  have hsing := binary_three_original_exterior_seed_singular c.L C W hLC K hBK
    σ hσ eK heK E hE y (hVZ (hUV hyU))
  have hvw : σ (f vv).val w=w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((σ (q ⟨v,hvz⟩) w).toMul:G)=u
    rw [hσ]
    change v*u*v⁻¹=u
    rw [←hvU u huU,mul_inv_cancel_right]
  have hvy : σ (f vv).val y=y := by
    change σ (f vv).val (σ (f aa).val w-w)=σ (f aa).val w-w
    rw [map_sub]
    have hc' : σ (f vv).val (σ (f aa).val w)=σ (f aa).val (σ (f vv).val w) := by
      rw [←Module.End.mul_apply,←Module.End.mul_apply,←map_mul,←map_mul]
      exact congrArg (fun k => σ k w) (congrArg (fun x : K => x.val)
        ((show Commute vv aa from (show Commute aa vv from Subtype.ext (Subtype.ext hav)).symm).map f).eq)
    rw [hc',hvw]
  have hEy : E y=E w ᵥ* Atlas.Order20160A8.Bivectors.compound (π aa)⁻¹.val-E w := by
    rw [map_sub,hE]
    rfl
  have hfixed : E y ᵥ* Atlas.Order20160A8.Bivectors.compound (π vv)⁻¹.val=E y := by
    have hh := hE (f vv) y
    rw [hvy] at hh
    exact hh.symm
  have he0 := singular_eq_zero_of_commuting_cubic_moving
    (π aa) (π vv) haPow hvPow hrank hcomm hv0 hva hva2 (E y) hsing
    (by exact ⟨E w,hEy.symm⟩) hfixed
  exact hy0 (E.injective (he0.trans E.map_zero.symm))

/-- The full original source forces the whole point span to be the marked
natural four-space, with the same quotient action and centralizing kernel. -/
theorem binary_three_source_four_natural_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2)
    (hz : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (c.L.subgroupOf C).map q
    let V := ⁅coreCenter c.L,c.L⁆
    let W := conjugateSpanBy V C
    ∃ hW : IsElementaryAbelian 2 W,
      let := hW
      ∃ σ : Representation (ZMod 2) (C ⧸ pCore 2 C) (Additive W),
        (∀ (x : C) (w : Additive W),
          ((σ (q x) w).toMul : G)=x*(w.toMul:G)*(x:G)⁻¹) ∧
        Function.Injective (σ.comp K.subtype) ∧
        σ.ker=centralizer (K : Set (C ⧸ pCore 2 C)) ∧
        ∃ eK : K ≃* SL(4,ZMod 2),
          (B.subgroupOf K).map eK.toMonoidHom=endpointParabolic ∧
          ∃ E : Additive W ≃ₗ[ZMod 2] (Fin 4 → ZMod 2),
            ∀ (k : K) (w : Additive W),
              E (σ k.val w)=E w ᵥ* survivorModelMatrix true ((eK k)⁻¹) := by
  obtain ⟨hW,σ,hσ,hinj,hker,eK,heK,dual,E,hE⟩ :=
    binary_three_source_four_standard_model
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
  let := hW
  cases dual with
  | true => exact ⟨hW,σ,hσ,hinj,hker,eK,heK,E,hE⟩
  | false =>
    exfalso
    have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
    have hnot : ¬ (d.T : Subgroup G) ≤ d.S := by
      intro hTS
      have ht : d.S.subgroupOf (d.T : Subgroup G) = ⊤ :=
        top_unique (fun x _ => hTS x.property)
      rw [ht,index_top] at hi
      omega
    obtain ⟨g,hgT,hgS⟩ := SetLike.not_le_iff_exists.mp hnot
    exact binary_three_source_exterior_model_impossible
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
      hz hz1 g hgT hgS σ hσ eK heK E hE

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
