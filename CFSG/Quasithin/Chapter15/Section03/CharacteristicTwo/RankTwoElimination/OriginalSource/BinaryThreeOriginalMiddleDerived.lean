module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalMiddleStructure
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSynchronizedSections
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointNaturalIrreducible
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The original middle derived group is the original natural eight

An intrinsic argument identifies D', without identifying the graph second
hat's named natural space with the original seed. The marked irreducible
section Phi/Z(Q), the order eight of D', and [Phi,Q]=H force D' into Z(Q).
Its L-displacement is nonzero because the entire L-fixed core factor has
order four. Irreducibility of the original natural seed then identifies D'.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem irreducible_section_dichotomy
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    {L D Z T : Subgroup G} {a : L →* A} {σ : Representation (ZMod 2) A V}
    [IsIrreducible σ] (ha : Function.Surjective a)
    (hs : HasSectionModel L D Z a σ)
    (hZT : Z ≤ T) (hTD : T ≤ D) (hLT : L ≤ normalizer T) : T = Z ∨ T = D := by
  obtain ⟨hZD,hLD,_,hn,e,he⟩ := hs
  let := hn
  let p := e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf D))
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : p.ker = Z.subgroupOf D := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let U : Subrepresentation σ := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 ((T.subgroupOf D).map p).toAddSubgroup'
    apply_mem_toSubmodule g := by
      intro v hv
      obtain ⟨l,rfl⟩ := ha g
      change Multiplicative.ofAdd v ∈ (T.subgroupOf D).map p at hv
      obtain ⟨x,hx,hv⟩ := hv
      let y := D.normalizerMonoidHom (inclusion hLD l) x
      have hyT : (y : G) ∈ T := (mem_normalizer_iff.mp (hLT l.property) x).mp hx
      change Multiplicative.ofAdd (σ (a l) v) ∈ (T.subgroupOf D).map p
      refine ⟨y,hyT,?_⟩
      apply Multiplicative.toAdd.injective
      have hh := he l x y rfl
      change (p y).toAdd = σ (a l) (p x).toAdd at hh
      rw [hh,hv]
      rfl }
  rcases eq_bot_or_eq_top U with hbot | htop
  · left
    apply le_antisymm ?_ hZT
    intro t ht
    have hv : (p ⟨t,hTD ht⟩).toAdd ∈ U := mem_map_of_mem p ht
    rw [hbot] at hv
    have hz : (⟨t,hTD ht⟩ : D) ∈ p.ker := hv
    rw [hk] at hz
    exact hz
  · right
    apply le_antisymm hTD
    intro d hd
    have hv : (p ⟨d,hd⟩).toAdd ∈ U := htop ▸ Submodule.mem_top
    change p ⟨d,hd⟩ ∈ (T.subgroupOf D).map p at hv
    obtain ⟨t,ht,heq⟩ := hv
    have hz : (⟨d,hd⟩ : D) / t ∈ p.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_div,heq,div_self']
    rw [hk] at hz
    have hh := T.mul_mem (hZT hz) ht
    change d / (t : G) * (t : G) ∈ T at hh
    simpa only [div_mul_cancel] using hh

omit [Finite G] in
private theorem normalizes_derived {A B : Subgroup G}
    (hAB : A ≤ normalizer B) : A ≤ normalizer (⁅B,B⁆ : Subgroup G) := by
  intro a ha
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hAB ha)]

/-- The original middle core has precisely the original natural eight as its derived subgroup. -/
theorem binary_three_large_distance_original_middle_derived
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
    let Q := LinearThree.commutatorCore c.L
    let D := Q ⊓ centralizer (frattiniIn Q : Set G)
    ⁅D,D⁆ = ⁅coreCenter c.L,c.L⁆ := by
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let ZQ := coreCenter c.L
  let D := Q ⊓ centralizer (Phi : Set G)
  let A := ⁅D,D⁆
  let V := ⁅ZQ,c.L⁆
  have hsizes := binary_three_large_distance_original_core_structure
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hAcard : Nat.card A = 8 := (binary_three_large_distance_original_middle_structure
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2
  have hZcard : Nat.card ZQ = 32 := by
    change Nat.card ((center Q).map Q.subtype) = 32
    rw [card_map_of_injective Q.subtype_injective]
    exact hsizes.2.1
  have hPhicard : Nat.card Phi = 256 := by
    change Nat.card ((frattini Q).map Q.subtype) = 256
    rw [card_map_of_injective Q.subtype_injective]
    exact hsizes.2.2.1
  have hPhi : Phi = ⁅Q,Q⁆ := by
    dsimp only [Phi,frattiniIn]
    rw [←hsizes.2.2.2.2.2.1,_root_.commutator_def,map_commutator,
      ←MonoidHom.range_eq_map,range_subtype]
  have hAPhi : A ≤ Phi := (commutator_mono inf_le_left inf_le_left).trans hPhi.symm.le
  have hPhiQ : Phi ≤ Q := map_subtype_le _
  have hZQ : ZQ ≤ Q := map_subtype_le _
  have hAQ : A ≤ Q := hAPhi.trans hPhiQ
  have hZcQ : ZQ ≤ centralizer (Q : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hQnPhi : Q ≤ normalizer Phi := Q.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Q (frattini Q))
  have hQD : Q ≤ normalizer D := (le_inf Q.le_normalizer
    (hQnPhi.trans (normalizer_le_normalizer_centralizer Phi))).trans
      inf_normalizer_le_normalizer_inf
  have hQA : Q ≤ normalizer A := normalizes_derived hQD
  obtain ⟨a,ha,_,hseed,hdual,hmiddle,_⟩ := binary_three_source_synchronized_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hLA : c.L ≤ normalizer A := normalizes_derived hmiddle.2.1
  have hLZ : c.L ≤ normalizer ZQ := hdual.2.2.1
  obtain ⟨common⟩ := t.commonFacts hc
  let earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hHF := (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.2
  have hHZ : intrinsicFour c.L ≤ ZQ := by
    intro x hx
    refine ⟨⟨x,(hHF hx).1⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext ((hHF hx).2 y
      (((LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)) y.property))
  have hPhiComm : ⁅Phi,Q⁆ = intrinsicFour c.L := by
    rw [hPhi]
    rfl
  have hAZ : A ≤ ZQ := by
    let : IsIrreducible BinaryLinearThree.W.dual := BinaryLinearThree.IrreducibleCatalogue.dual_irreducible
    have hjoin : c.L ≤ normalizer (A ⊔ ZQ : Subgroup G) :=
      (le_inf hLA hLZ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    rcases irreducible_section_dichotomy ha hdual le_sup_right
      (sup_le hAPhi hdual.1) hjoin with he | he
    · exact (show A ≤ A ⊔ ZQ from le_sup_left).trans he.le
    · have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes A ZQ
        ((hZcQ.trans (centralizer_le hAQ)).trans (Subgroup.centralizer_le_normalizer _))
      change A ⊔ ZQ = Phi at he
      rw [hAcard,hZcard,he,hPhicard] at hc
      have hint : A ⊓ ZQ = ⊥ := Subgroup.card_eq_one.mp (by omega)
      have hcomm : ⁅A,Q⁆ = ⊥ := le_bot_iff.mp ((le_inf
        (le_normalizer_iff_commutator_le_left.mp hQA)
        ((commutator_mono hAPhi le_rfl).trans (hPhiComm.le.trans hHZ))).trans hint.le)
      have hcQ : A ≤ centralizer (Q : Set G) := commutator_eq_bot_iff_le_centralizer.mp hcomm
      intro x hx
      exact ⟨⟨x,hAQ hx⟩,mem_center_iff.mpr (fun y => Subtype.ext (hcQ hx y y.property)),rfl⟩
  have hmove : ⁅A,c.L⁆ ≠ ⊥ := by
    intro hz
    have hAc : A ≤ centralizer (c.L : Set G) := commutator_eq_bot_iff_le_centralizer.mp hz
    have hAF : A ≤ coreFixed c.L := le_inf hAQ hAc
    have hbound := card_le_of_le hAF
    rw [hAcard,(binary_three_large_distance_fixed_factor_bound
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).1] at hbound
    omega
  have hmoveV : ⁅A,c.L⁆ = V := binary_three_source_natural_invariant_eq
    d c.L b t common hb _ V (commutator_mono hAZ le_rfl)
      (normalizer_commutator_ge_right _ _) hmove rfl
  have hVA : V ≤ A := hmoveV.symm.le.trans (le_normalizer_iff_commutator_le_left.mp hLA)
  have hVcard : Nat.card V = 8 := by
    obtain ⟨_,_,_,hn,ev,_⟩ := hseed
    let := hn
    have he : Nat.card (V ⧸ (⊥ : Subgroup G).subgroupOf V) = 8 := by
      rw [Nat.card_congr ev.toEquiv]
      change Nat.card (Fin 3 → ZMod 2) = 8
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Module.finrank_pi,
        Fintype.card_fin,Nat.card_zmod]
      norm_num
    simpa only [bot_subgroupOf,Nat.card_congr (QuotientGroup.quotientBot (G := V)).toEquiv] using he
  exact (eq_of_le_of_card_ge hVA (by rw [hVcard,hAcard])).symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
