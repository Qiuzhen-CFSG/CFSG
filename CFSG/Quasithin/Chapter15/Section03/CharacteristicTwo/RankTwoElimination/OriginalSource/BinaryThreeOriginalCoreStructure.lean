module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeFixedFactorBound
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.FrattiniSections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.FixedFactorReduction
public import Theory.Frattini.OmegaProducts

/-!
# Exact original core structure from the whole-factor exchange bound

The original exchanger bounds the whole component-fixed factor by four.
Its literal pullback through the replacement and amalgam embedding therefore
equals H. The first-hat intersection and Frattini calculations now apply
without a separate moving-index hypothesis: the moving layer is the derived
and Frattini subgroup and has index4096. The center has order32, the Frattini
subgroup order256, and the whole core order2^20.

These conclusions retain the original replacement and original core. They
do not make the original O₂(LS) fix H, and do not assert a finite-carrier
exclusion or the false universal MS classification.

Source: Aschbacher--Smith15.3.23, pp.1128--1129; MS93(4.5)(iii)--(vii),
pp.895--900, and the characteristic replacement in Section7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The whole graph fixed factor is the intrinsic source four, using the
actual original exchanger and both literal inclusions. -/
theorem source_fixedFactor_eq_H_of_original_exchange
    (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let R := t.reduction.radical
    core R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) =
      H R (alpha R) := by
  let J := L ⊔ d.S
  let M := t.reduction.overgroup
  let R := t.reduction.radical
  let K := core R (alpha R)
  let F := K ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))
  let L₀ := (L.subgroupOf J).subgroupOf M
  let ι : M →* G := J.subtype.comp M.subtype
  let emb := embedM R
  have hi : Function.Injective ι := J.subtype_injective.comp M.subtype_injective
  have hLe : L₀.map emb = Ltilde R (alpha R) := t.Ltilde_embedded.symm
  have hLi : L₀.map ι = L := by
    dsimp only [ι,L₀]
    rw [←map_map,map_subgroupOf_eq_of_le (show L.subgroupOf J ≤ M from le_sup_left),
      map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left)]
  have hKe : K ≤ emb.range := by
    have hh : K ≤ stabilizer R (alpha R) :=
      (DistanceTwo.core_le_Q _).trans (fun _ hx => hx.1)
    simpa only [alpha,stabilizer_m_base,Mbar] using hh
  have hFe : (F.comap emb).map emb = F := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr (inf_le_left.trans hKe)
  have hKi : (K.comap emb).map ι = commutatorCore L := by
    dsimp only [ι]
    rw [←map_map,t.core_pullback]
    exact sourceQ_map_subtype (show L ≤ J from le_sup_left) b.component
  have hFi : (F.comap emb).map ι ≤ coreFixed L := by
    rintro x ⟨a,ha,rfl⟩
    refine ⟨hKi ▸ mem_map_of_mem ι ha.1,?_⟩
    intro l hl
    rw [←hLi] at hl
    obtain ⟨l,hl,rfl⟩ := hl
    rw [←map_mul,←map_mul]
    apply congrArg ι
    apply embedM_injective R
    simpa only [map_mul] using ha.2 (emb l) (hLe ▸ mem_map_of_mem emb hl)
  have hcard : Nat.card F ≤ 4 := by
    rw [←hFe,card_map_of_injective (embedM_injective R),
      ←card_map_of_injective (f := ι) hi]
    exact (card_le_of_le hFi).trans_eq
      (coreFixed_card_eq_four_of_original_exchange d L e h hg b t common earlier g hgT hgS)
  have hH : Nat.card (H R (alpha R)) = 4 := Nat.le_antisymm
    (DistanceEight.CoreFactors.Early.H_card_le_four common earlier rfl)
    (DistanceEight.CoreFactors.Early.First.Layer.H_card_lower common earlier (alpha R) rfl)
  let : Finite K := DistanceTwo.finite_core (alpha R)
  let : Finite F := Finite.of_injective (inclusion (show F ≤ K from inf_le_left))
    (inclusion_injective _)
  exact (eq_of_le_of_card_ge (earlier.factor_inclusions common).1
    (hcard.trans_eq hH.symm)).symm

/-- The actual source fixed-factor equality gives exact derived, Frattini,
center and order data, including the formerly missing moving index4096. -/
theorem source_core_structure_of_original_exchange
    (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let R := t.reduction.radical
    let K := core R (alpha R)
    (frattini K).map K.subtype = Vcirc R (alpha R) ∧
      ⁅K,K⁆ = Vcirc R (alpha R) ∧ (Vcirc R (alpha R)).relIndex K = 4096 ∧
      Nat.card (center K) = 32 ∧ Nat.card (frattini K) = 256 ∧
      Nat.card K = 1048576 ∧ center K ≤ frattini K := by
  let R := t.reduction.radical
  let K := core R (alpha R)
  have hfixed := source_fixedFactor_eq_H_of_original_exchange
    d L e h hg b t common earlier g hgT hgS
  let : Finite K := DistanceTwo.finite_core (alpha R)
  let : Fact (IsPGroup 2 K) := ⟨(Q_isPGroup R t.source.two_group t.source.core_le _ rfl).to_le
    (DistanceTwo.core_le_Q _)⟩
  obtain ⟨p⟩ := DistanceEight.CoreFactors.Early.sourcePath_nonempty t.source common earlier (alpha R) rfl
  have hphi := DistanceEight.CoreFactors.Center.core_frattini_eq_moving_of_fixedFactor
    common earlier hfixed
  have hderived : ⁅K,K⁆ = Vcirc R (alpha R) := by
    apply le_antisymm ?_ (DistanceEight.CoreFactors.Center.moving_le_core_derived common earlier p)
    rw [←hphi]
    have hh := map_mono (f := K.subtype) (commutator_le_frattini_of_isPGroup (R := K) (p := 2))
    simpa only [commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
  have hindex : (Vcirc R (alpha R)).relIndex K = 4096 := by
    rw [←DistanceEight.CoreFactors.Center.core_inf_first_eq_moving_of_fixedFactor common earlier hfixed p,
      inf_relIndex_left]
    exact DistanceEight.CoreFactors.Center.core_first_relIndex_eq_fourThousandNinetySix common earlier p
  have hcenter : Nat.card (center K) = 32 :=
    DistanceEight.CoreFactors.Center.core_center_card_of_moving_index_bound common earlier hindex.le
  let Phi := (frattini K).map K.subtype
  let Z₀ := (center K).map K.subtype
  obtain ⟨s⟩ := DistanceEight.CoreFactors.Center.frattini_marked_dual_of_fixedFactor common earlier hfixed
  have hZindex : Z₀.relIndex Phi = 8 := by
    change (Z₀.subgroupOf Phi).index = 8
    rw [←s.kernel,index_ker,s.quotient.range_eq_top_of_surjective s.onto,card_top]
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
    norm_num
  have hZcard : Nat.card Z₀ = 32 := by
    rw [card_map_of_injective K.subtype_injective,hcenter]
  have hphicard : Nat.card (frattini K) = 256 := by
    have ht := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R)) Z₀ Phi bot_le s.lower_le
    rw [relIndex_bot_left,relIndex_bot_left,hZindex,hZcard,
      card_map_of_injective K.subtype_injective] at ht
    exact ht.symm
  have hKcard : Nat.card K = 1048576 := by
    have ht := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R)) Phi K bot_le (map_subtype_le _)
    rw [relIndex_bot_left,relIndex_bot_left,show Phi = Vcirc R (alpha R) from hphi,
      hindex] at ht
    have hc : Nat.card (Vcirc R (alpha R)) = 256 := by
      rw [←hphi,card_map_of_injective K.subtype_injective,hphicard]
    rw [hc] at ht
    exact ht.symm
  exact ⟨hphi,hderived,hindex,hcenter,hphicard,hKcard,
    DistanceEight.CoreFactors.Center.core_center_le_frattini_of_fixedFactor common earlier hfixed⟩

/-- The exact core invariants are transported to the original ambient Q,
including its own center, derived subgroup and Frattini subgroup. -/
theorem original_core_structure_of_exchange
    (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let Q := commutatorCore L
    Nat.card (center Q) = 32 ∧ Nat.card (frattini Q) = 256 ∧
      Nat.card Q = 1048576 ∧ center Q ≤ frattini Q ∧
      _root_.commutator Q = frattini Q ∧ (frattini Q).index = 4096 := by
  let J := L ⊔ d.S
  let R := t.reduction.radical
  let K := core R (alpha R)
  let Q := commutatorCore L
  let Q₀ := BinaryMS.commutatorCore (L.subgroupOf J)
  have hQ : Q₀.map J.subtype = Q := sourceQ_map_subtype
    (show L ≤ J from le_sup_left) b.component
  let a : K ≃* Q := t.coreEquiv.trans
    ((Q₀.equivMapOfInjective J.subtype J.subtype_injective).trans (MulEquiv.subgroupCongr hQ))
  obtain ⟨hphi,hderived,hindex,hcenter,hphicard,hKcard,hZphi⟩ :=
    source_core_structure_of_original_exchange d L e h hg b t common earlier g hgT hgS
  have hroot : _root_.commutator K = frattini K := by
    apply map_injective K.subtype_injective
    simpa only [commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype]
      using hderived.trans hphi.symm
  have hPhiindex : (frattini K).index = 4096 := by
    have hm := relIndex_map_map_of_injective (frattini K) (⊤ : Subgroup K) K.subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype,relIndex_top_right,hphi,hindex] at hm
    exact hm.symm
  refine ⟨(Nat.card_congr (centerCongr a).symm.toEquiv).trans hcenter,?_,
    (Nat.card_congr a.symm.toEquiv).trans hKcard,?_,?_,?_⟩
  · rw [←frattini_map_equiv a,card_map_of_injective a.injective]
    exact hphicard
  · intro z hz
    have hzK : a.symm z ∈ center K := (centerCongr a.symm ⟨z,hz⟩).property
    rw [←frattini_map_equiv a]
    exact ⟨a.symm z,hZphi hzK,a.apply_symm_apply z⟩
  · have hm := congrArg (Subgroup.map a.toMonoidHom) hroot
    rw [frattini_map_equiv,map_commutator_eq,MonoidHom.range_eq_top.mpr a.surjective] at hm
    exact hm
  · have hm := relIndex_map_map_of_injective (f := a.toMonoidHom)
      (frattini K) (⊤ : Subgroup K) a.injective
    rw [frattini_map_equiv,←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr a.surjective,
      relIndex_top_right,relIndex_top_right] at hm
    exact hm.trans hPhiindex

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The complete original large-distance prefix supplies the exact core
orders and Frattini/derived identity, without any quotient-bound premise. -/
theorem binary_three_large_distance_original_core_structure
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
    let R := t.reduction.radical
    let Q := LinearThree.commutatorCore c.L
    (Vcirc R (alpha R)).relIndex (core R (alpha R)) = 4096 ∧
      Nat.card (center Q) = 32 ∧ Nat.card (frattini Q) = 256 ∧
      Nat.card Q = 1048576 ∧ center Q ≤ frattini Q ∧
      _root_.commutator Q = frattini Q ∧ (frattini Q).index = 4096 := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hnot : ¬ (d.T : Subgroup G) ≤ d.S := by
    intro hTS
    have ht : d.S.subgroupOf (d.T : Subgroup G) = ⊤ := top_unique (fun x _ => hTS x.property)
    rw [ht,index_top] at hi
    omega
  obtain ⟨g,hgT,hgS⟩ := SetLike.not_le_iff_exists.mp hnot
  exact ⟨(source_core_structure_of_original_exchange
      d c.L eSL h hg b t common earlier g hgT hgS).2.2.1,
    original_core_structure_of_exchange d c.L eSL h hg b t common earlier g hgT hgS⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
