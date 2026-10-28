module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeFixedFactorPair
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeReplacementGeometry
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# The original exchanger bounds the entire component-fixed factor

The full fixed part C of the replacement vertex omega-center is central in
that replacement stabilizer, so C lies in its edge omega-center E. The natural
three-space splitting and actual edge index give |E:C|=4. The whole original
component-fixed factor F lies in C. Since E is characteristic in the original
S, the actual exchanger in T minus S also puts Fᵍ inside E. The original
opposite-residual action makes Fᵍ disjoint from C, so |F|≤4. The intrinsic
four lies in F and therefore F is exactly that four.

All transports use the same replacement, core, component and subgroup
inclusions. This is an original Chapter15 source bound; it does not assert
the analogous fixed-factor theorem for arbitrary MS93 inputs or centrality
under the larger original O₂(LS).

Source: Aschbacher--Smith15.3.8,15.3.12,15.3.23, pp.1123--1129;
MS93(4.5.1) and the characteristic replacement in Section7.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

private theorem edge_fixed_part_card
    {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    {geometry : Geometry R} {source : LocalSource L R}
    (common : CommonFacts R source geometry)
    (earlier : DistanceEight.CoreFactors.Earlier R geometry) :
    let C := Z R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))
    C ≤ Z R (beta R) ∧ Nat.card (Z R (beta R)) = 4 * Nat.card C := by
  let C := Z R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))
  have hCE : C ≤ Z R (beta R) := by
    intro x hx
    have hxX : x ∈ X R (alpha R) := by
      rw [common.X_eq_Z (alpha R) rfl]
      exact hx.1
    have hfix := ((source.X_fixed_eq_stabilizer_fixed (alpha R) rfl).le ⟨hxX,hx.2⟩).2
    change x ∈ omegaCenter (Q R (beta R))
    apply mem_omegaCenter_iff.mpr
    refine ⟨Q_le_adjacent_h R rfl (base_adjacent R) (omegaCenter_le _ hxX),
      (mem_omegaCenter_iff.mp hxX).2.1,?_⟩
    intro y hy
    exact hfix y (hy.2 _ (adjacent_symm R (base_adjacent R)))
  let := finite_Z R (alpha R)
  let := finite_Z R (beta R)
  let : Finite C := Finite.of_injective (inclusion (show C ≤ Z R (alpha R) from inf_le_left))
    (inclusion_injective _)
  have hCZ : Nat.card (Z R (alpha R)) = 8 * Nat.card C := by
    rw [common.decomposition,
      card_sup_eq_mul_of_normalizes_of_disjoint _ _
        ((inf_le_left.trans (Z_le_stabilizer R _)).trans (U_normalized _)) common.disjoint,
      common.natural.card]
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (Z R (beta R)) (Z R (alpha R)) bot_le
    (Escape.EdgeTransfer.edge_Z_le _ _ rfl (base_adjacent R))
  rw [relIndex_bot_left,relIndex_bot_left,
    earlier.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R),hCZ] at hcount
  refine ⟨hCE,?_⟩
  change Nat.card (Z R (beta R)) = 4 * Nat.card C
  omega

/-- The actual exchanger bounds the whole original fixed factor by four.
Neither an order-four premise nor an original radical action bound is assumed. -/
theorem coreFixed_card_eq_four_of_original_exchange
    (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    Nat.card (coreFixed L) = 4 := by
  let J := L ⊔ d.S
  let M := t.reduction.overgroup
  let R := t.reduction.radical
  let L₀ := (L.subgroupOf J).subgroupOf M
  let ι : M →* G := J.subtype.comp M.subtype
  have hi : Function.Injective ι := J.subtype_injective.comp M.subtype_injective
  let emb := embedM R
  let Cg := Z R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))
  let C₀ := Cg.comap emb
  let E₀ := omegaCenter R
  let C := C₀.map ι
  let E := E₀.map ι
  have hLe : L₀.map emb = Ltilde R (alpha R) := t.Ltilde_embedded.symm
  have hLi : L₀.map ι = L := by
    dsimp only [ι,L₀]
    rw [←map_map,map_subgroupOf_eq_of_le (show L.subgroupOf J ≤ M from le_sup_left),
      map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left)]
  have hCe : C₀.map emb = Cg := by
    rw [map_comap_eq]
    apply inf_eq_right.mpr
    change Cg ≤ Mbar R
    exact inf_le_left.trans (by
      simpa only [alpha,stabilizer_m_base] using Z_le_stabilizer R (alpha R))
  have hEe : E₀.map emb = Z R (beta R) := by
    change (omegaCenter R).map emb = omegaCenter (Q R (beta R))
    rw [Q_beta,omegaCenter_map R emb (embedM_injective R)]
  obtain ⟨hCEg,hcountg⟩ := edge_fixed_part_card common earlier
  have hC₀E₀ : C₀ ≤ E₀ := by
    apply (map_le_map_iff_of_injective (embedM_injective R)).mp
    rw [hCe,hEe]
    exact hCEg
  have hCE : C ≤ E := map_mono hC₀E₀
  have hcount : Nat.card E = 4 * Nat.card C := by
    have hcard := hcountg
    change Nat.card (Z R (beta R)) = 4 * Nat.card Cg at hcard
    rw [←hEe,←hCe,card_map_of_injective (embedM_injective R),
      card_map_of_injective (embedM_injective R)] at hcard
    dsimp only [E,C]
    rw [card_map_of_injective hi,card_map_of_injective hi]
    exact hcard
  have hCL : C ≤ centralizer (L : Set G) := by
    rintro x ⟨a,ha,rfl⟩
    intro l hl
    rw [←hLi] at hl
    obtain ⟨l,hl,rfl⟩ := hl
    have hlL : emb l ∈ Ltilde R (alpha R) := by
      rw [←hLe]
      exact mem_map_of_mem emb hl
    have hh : l * a = a * l := (embedM_injective R) (by
      simpa only [map_mul] using ha.2 (emb l) hlL)
    simpa only [map_mul] using congrArg ι hh
  let K₀ : Subgroup M := ⁅pCore 2 M,L₀⁆
  have hKe : K₀.map emb = core R (alpha R) :=
    (core_alpha R t.source.two_group t.source.core_le t.source.residual).symm
  have hKi : K₀.map ι = commutatorCore L := by
    dsimp only [ι,K₀,L₀]
    rw [←map_map,t.reduction.commutatorCore_eq b]
    exact sourceQ_map_subtype (show L ≤ J from le_sup_left) b.component
  have hFC : coreFixed L ≤ C := by
    rintro x ⟨hx,hxL⟩
    rw [←hKi] at hx
    obtain ⟨a,ha,rfl⟩ := hx
    apply mem_map_of_mem ι
    have haK : emb a ∈ core R (alpha R) := hKe ▸ mem_map_of_mem emb ha
    have haL : emb a ∈ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) := by
      intro l hl
      rw [←hLe] at hl
      obtain ⟨l,hl,rfl⟩ := hl
      have hlL : ι l ∈ L := hLi.le (mem_map_of_mem ι hl)
      have hh : l*a = a*l := hi (by simpa only [map_mul] using hxL (ι l) hlL)
      simpa only [←map_mul] using congrArg emb hh
    exact ⟨DistanceEight.CoreFactors.Center.core_fixedFactor_le_Z common earlier ⟨haK,haL⟩,haL⟩
  have hEO : E = omegaCenter (t.reduction.ambient.map J.subtype) := by
    dsimp only [E,E₀,ι]
    rw [←map_map,←omegaCenter_map _ M.subtype M.subtype_injective,
      map_subgroupOf_eq_of_le (show t.reduction.ambient ≤ M from le_sup_right),
      ←omegaCenter_map _ J.subtype J.subtype_injective]
  have hEn : (d.T : Subgroup G) ≤ normalizer (E : Set G) := by
    let := t.replacementOmega_characteristic
    have hiS := d.action.planeStabilizer_index_two d.T d.sylow_le 1
    have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
        (normal_of_index_eq_two hiS)
    have hn := normalizer_le_normalizer_characteristic_map
      J.subtype J.subtype_injective (d.S.subgroupOf J) t.replacementOmega
    rw [map_subgroupOf_eq_of_le (show d.S ≤ J from le_sup_right)] at hn
    have he : (t.replacementOmega.map (d.S.subgroupOf J).subtype).map J.subtype = E := by
      rw [t.replacementOmega_map, map_map]
    rw [he] at hn
    exact hTS.trans hn
  have hFgE : (coreFixed L).conjBy g ≤ E := by
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) (hFC.trans hCE)
    have he : E.map (MulAut.conj g).toMonoidHom = E :=
      mem_normalizer_iff_map_conj_eq.mp (hEn hgT)
    rwa [he] at hm
  have hback : (YC d L).conjBy g = YL d L :=
    ThreeLayer.exchange_back d L (d.action.planeStabilizer_index_two d.T d.sylow_le 1)
      (le_sup_right.trans hg.component_residual_normalized) g hgT (hg.exchange g hgT hgS)
  have hdis : Disjoint ((coreFixed L).conjBy g) C := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    rintro x ⟨⟨f,hf,rfl⟩,hxC⟩
    have hfYC : f ∈ centralizer (YC d L : Set G) := by
      intro y hy
      apply (MulAut.conj g).injective
      have hyL : (MulAut.conj g) y ∈ YL d L := hback ▸ mem_map_of_mem _ hy
      have hh := (hCL hxC) ((MulAut.conj g) y)
        (((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right) hyL)
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using hh
    have hf1 : f = 1 := (coreFixed_opposite_residual_fixed_eq_bot d L e h hg b t common earlier).le
      ⟨hf,hfYC⟩
    simpa only [hf1,map_one] using (one_mem (⊥ : Subgroup G))
  let : IsElementaryAbelian 2 E := by
    rw [hEO]
    exact omegaCenter_elementary _
  have hcomm : C ≤ centralizer ((coreFixed L).conjBy g : Set G) :=
    hCE.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hFgE))
  have hbound := card_le_of_le (sup_le hFgE hCE)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hcomm.trans (Subgroup.centralizer_le_normalizer _)) hdis,hcount] at hbound
  have hconj : Nat.card ((coreFixed L).conjBy g) = Nat.card (coreFixed L) :=
    card_map_of_injective (MulAut.conj g).injective
  rw [hconj] at hbound
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hlo := card_le_of_le (intrinsicFour_properties_of_MS93 d L b t common earlier).2.2
  rw [(intrinsicFour_properties_of_MS93 d L b t common earlier).2.1] at hlo
  nlinarith

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.CoreActions LinearThree.Extension.SourceCases
open LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full original large-distance source identifies its entire component-fixed
factor with the intrinsic four. The original radical fixes this whole factor,
and its two exchanged copies recover the original module. -/
theorem binary_three_large_distance_fixed_factor_bound
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
    (hb : 4 < t.geometry.b t.reduction.radical) :
    Nat.card (coreFixed c.L) = 4 ∧ coreFixed c.L = intrinsicFour c.L ∧
      d.R ≤ centralizer (coreFixed c.L : Set G) ∧
      ∀ g : G, g ∈ (d.T : Subgroup G) → g ∉ d.S →
        coreFixed c.L ⊔ (coreFixed c.L).conjBy g = d.V := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hgexists : ∃ g : G, g ∈ (d.T : Subgroup G) ∧ g ∉ d.S := by
    by_contra! hall
    have htop : d.S.subgroupOf (d.T : Subgroup G) = ⊤ := by
      apply top_unique
      intro x _
      exact hall x x.property
    have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
    change (d.S.subgroupOf (d.T : Subgroup G)).index = 2 at hi
    rw [htop,index_top] at hi
    omega
  obtain ⟨g,hgT,hgS⟩ := hgexists
  have hcard := coreFixed_card_eq_four_of_original_exchange d c.L eSL h hg b t
    common earlier g hgT hgS
  have hfour := intrinsicFour_properties_of_MS93 d c.L b t common earlier
  have heq : coreFixed c.L = intrinsicFour c.L :=
    (eq_of_le_of_card_ge hfour.2.2 (by rw [hcard,hfour.2.1])).symm
  refine ⟨hcard,heq,
    radical_centralizes_coreFixed_of_MS93 d c.L eSL h hg b t common earlier hcard,?_⟩
  intro g hgT hgS
  rw [heq,intrinsicFour_conjugate_eq_movingPlane_of_MS93
    d c.L eSL h hg b t common earlier g hgT hgS]
  obtain ⟨i,_,_,_,hC,_,hsup,_⟩ := hg.coordinates
  have hH : intrinsicFour c.L = d.action.plane i :=
    (intrinsicFour_eq_complementary_plane_of_MS93 d c.L eSL h hg b t common earlier).trans hC
  rw [hH,sup_comm]
  exact hsup

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
