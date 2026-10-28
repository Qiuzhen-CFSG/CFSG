module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanCoreCenter
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanComponentWitness
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanPromotedCore
public import Theory.GroupTheory.PGroup.CentralOmegaDetection
public import Theory.GroupTheory.PerfectSimpleQuotientDetection

/-!
# The actual normalizer-core center is elementary

Its squares centralize L because [Z(F),L]=Phi(Q) is elementary.
The promoted simple quotient makes the entire component centralize these
squares. The original residual subgroup has trivial centralizer in S,
so every square is trivial.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem original_residual_sylow_centralizer
    (d : LocalData G) (hfixed : fixedPlane d.V d.Yplus = ⊥) :
    d.S ⊓ centralizer (d.Yplus : Set G) = ⊥ := by
  apply inf_centralizer_eq_bot_of_central_involutions d.S d.Yplus
    (d.T.isPGroup'.to_le inf_le_left)
    (le_sup_right.trans (OutsideStructure.LocalBranches.ys_normalizes_yplus d))
  intro x hx hxS hxY hx2
  have hxO : x ∈ centralOmegaIn d.S :=
    (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hx,hx2,hxS⟩
  rw [←(source_lemma_15_3_8 d.T d.action d.sylow_le 1).1] at hxO
  exact hfixed.le ⟨hxO.1,hxY⟩

/-- All elements in the center of the actual fixed-span normalizer core
have square one. -/
theorem binary_three_source_fixed_span_core_center_elementary
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
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G)))
    (hK : K.IsCComponent) (hKn : K.Normal)
    (hLK : c.L.subgroupOf (centralizer ({z} : Set G)) ≤ K)
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))]
    (eB : (((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) ⧸
      pCore 2 ((c.L.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) ≃* PSL(3,ZMod 2))
    (hrX : primeRank 3 (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))) = 2)
    (hrB : primeRank 3 (normalizer ((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))) ≤ 1)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) 4 2) :
    let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
    let F := (normalizer (U : Set G)).pCoreIn 2
    let ZF := (center F).map F.subtype
    IsElementaryAbelian 2 ZF := by
  let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
  let A := normalizer (U : Set G)
  let F := A.pCoreIn 2
  let ZF := (center F).map F.subtype
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let W := conjugateSpanBy ⁅coreCenter c.L,c.L⁆ (centralizer ({z} : Set G))
  obtain ⟨D,hD,hDn,hLD,hfull,hker,hJ,hSJ,hchar,htwoJ,hJA,
    c5,hc5,⟨e5⟩,hY,hθJ,hθNU,hθM⟩ :=
    binary_three_source_fixed_span_component_witness
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm
  have hBA : c5.L ≤ A := by rw [hc5]; exact map_subtype_le D
  have hout := binary_three_source_fixed_span_outside
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hLA : c.L ≤ A := le_sup_left.trans hout.2.1
  have hLB : c.L ≤ c5.L := by
    rw [hc5]
    intro x hx
    exact ⟨⟨x,hLA hx⟩,hLD hx,rfl⟩
  have hAZ : A ≤ normalizer (ZF : Set G) := A.le_normalizer.trans
    ((normalizer_le_normalizer_characteristic_image A (pCore 2 A)).trans
      (normalizer_le_normalizer_characteristic_image F (center F)))
  have hBZ : c5.L ≤ normalizer (ZF : Set G) := hBA.trans hAZ
  have hLZ : c.L ≤ normalizer (ZF : Set G) := hLB.trans hBZ
  obtain ⟨S,hS⟩ := hout.2.2.2.1
  have hFS : F ≤ d.S := hS ▸ pCoreIn_le_sylow A S
  have hZS : ZF ≤ d.S := (map_subtype_le _).trans hFS
  let : IsMulCommutative ZF := map_isMulCommutative _ _
  let sq : ZF →* G := ZF.subtype.comp (powMonoidHom 2)
  let E := sq.range
  have hES : E ≤ d.S := by
    rintro _ ⟨x,rfl⟩
    exact d.S.pow_mem (hZS x.property) 2
  have hBE : c5.L ≤ normalizer (E : Set G) := by
    apply le_normalizer_iff.mpr
    rintro a ha _ ⟨x,rfl⟩
    let y : ZF := ⟨a*(x:G)*a⁻¹,(le_normalizer_iff.mp hBZ) a ha x x.property⟩
    refine ⟨y,?_⟩
    change (a*(x:G)*a⁻¹)^2 = a*(x:G)^2*a⁻¹
    exact (map_pow (MulAut.conj a).toMonoidHom (x:G) 2).symm
  have hmove : ⁅ZF,c.L⁆ = Phi := (binary_three_source_fixed_span_core_center
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).2.2
  have hPhi : Phi = U ⊔ ⁅coreCenter c.L,c.L⁆ :=
    (binary_three_source_fixed_span_frattini_pairing
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm).1
  let : IsElementaryAbelian 2 (U ⊔ W : Subgroup G) :=
    (binary_three_source_fixed_span_promoted_core
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm).2.1
  have hPhiUW : Phi ≤ U ⊔ W := by
    rw [hPhi]
    exact sup_le_sup_left (le_conjugateSpanBy _ _) _
  let : IsElementaryAbelian 2 Phi :=
    IsElementaryAbelian.of_injective (inclusion hPhiUW) (inclusion_injective hPhiUW)
  have hEL : E ≤ centralizer (c.L : Set G) := by
    rintro _ ⟨x,rfl⟩ l hl
    have hm : ⁅(x:G),l⁆ ∈ Phi :=
      hmove ▸ commutator_mem_commutator x.property hl
    have hmZ : ⁅(x:G),l⁆ ∈ ZF :=
      (le_normalizer_iff_commutator_le_left.mp hLZ)
        (commutator_mem_commutator x.property hl)
    have hh : (x:G)*⁅(x:G),l⁆ = ⁅(x:G),l⁆*(x:G) :=
      congrArg Subtype.val (mul_comm x (⟨_,hmZ⟩ : ZF))
    have hfix : (x:G)*⁅(x:G),l⁆*(x:G)⁻¹ = ⁅(x:G),l⁆ := by
      rw [hh,mul_inv_cancel_right]
    have hpow : ⁅(x:G),l⁆^2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hm
    have hcomm : ⁅(x:G)^2,l⁆ = 1 := by
      rw [pow_two,commutatorElement_mul_left_eq_conj_mul,hfix,←pow_two,hpow]
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
  let CB := (centralizer (E : Set G)).subgroupOf c5.L
  let : CB.Normal := normal_subgroupOf_of_le_normalizer
    (hBE.trans (normalizer_le_normalizer_centralizer E))
  have hperfect := c5.component.perfect
  let := hperfect
  let : Group.IsPerfect c5.L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe c5.le_thompson).toMonoidHom)
    (subgroupOfEquivOfLe c5.le_thompson).surjective
  let : IsSimpleGroup PSL(5,ZMod 2) := Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup (c5.L ⧸ pCore 2 c5.L) := e5.isSimpleGroup
  let : Group.IsNilpotent (pCore 2 c5.L) := pCore_isPGroup.isNilpotent
  have hLC : c.L.subgroupOf c5.L ≤ CB := fun x hx =>
    (le_centralizer_iff.mp hEL) hx
  have hnot : ¬ CB ≤ pCore 2 c5.L := by
    intro hh
    have hLp : IsPGroup 2 c.L := (c5.L.isPGroup_pCoreIn 2).to_le (by
      intro x hx
      exact mem_map_of_mem c5.L.subtype (hh (hLC (show (⟨x,hLB hx⟩ : c5.L) ∈ c.L.subgroupOf c5.L from hx))))
    let : Group.IsNilpotent c.L := hLp.isNilpotent
    have hs : Group.IsSolvable (c.L.subgroupOf (c.L ⊔ d.S)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (show c.L ≤ c.L ⊔ d.S from le_sup_left)).toMonoidHom)
        (subgroupOfEquivOfLe (show c.L ≤ c.L ⊔ d.S from le_sup_left)).injective
    exact b.component.not_isSolvable hs
  have hCB : CB = ⊤ := eq_top_of_not_le_solvable_simple_quotient (pCore 2 c5.L) CB hnot
  have hEB : E ≤ centralizer (c5.L : Set G) := by
    apply le_centralizer_iff.mp
    intro x hx
    exact (show (⟨x,hx⟩ : c5.L) ∈ CB from hCB.symm ▸ mem_top _)
  obtain ⟨hW0,hJ0,hcore0,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW0 hJ0 hcore0
  have hfixed : fixedPlane d.V d.Yplus = ⊥ := by
    rw [hg.first_choice]
    exact d.action.fixedPlane_eq_bot_of_residual_image
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) h.image
  have hEbot : E = ⊥ := bot_unique ((le_inf hES
    (hEB.trans (centralizer_le hY))).trans_eq (original_residual_sylow_centralizer d hfixed))
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro x
  apply Subtype.ext
  exact hEbot.le (show sq x ∈ E from ⟨x,rfl⟩)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
