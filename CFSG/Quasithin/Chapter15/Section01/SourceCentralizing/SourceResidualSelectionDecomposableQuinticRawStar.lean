module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawComponent
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedAlternative
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.FullSylowBlocks
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Raw quintic components yield rank-one blocks or the actual C.2.7 catalogue

The literal radical Q=O₂(H∩Mc), its characteristic-normalizer control and
its exact normalizer in H supply C.2.4. A full Sylow intersection gives a
chi-zero block; nonsolvability removes the alternating-three case. In the
other branch Q normalizes the same component L and supplies the genuine
C.2.7 input, star model and central comparison kernel.

The original order-four partner source retains its actual component and
all earlier raw facts. No generation of M by its marked centralizer and T
is assumed, and no CaseIComponentData record is introduced.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
open ChapterC ChapterC.C27Source ChapterC.CatalogueFullSylow
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem raw_normal_core_sylow_closure (R N : Subgroup G)
    (hRN : R ≤ N) (hp : IsPGroup 2 R) (hn : N ≤ normalizer (R : Set G)) :
    IsSylowInNormalClosure R N := by
  let : (R.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hn
  unfold IsSylowInNormalClosure
  rw [normalClosure_eq_self]
  have hpR : IsPGroup 2 (R.subgroupOf N) := hp.comap_subtype
  let hp' : IsPGroup 2 (⊤ : Subgroup (R.subgroupOf N)) := hpR.of_equiv topEquiv.symm
  let P : Sylow 2 (R.subgroupOf N) :=
    ⟨⊤,hp',fun _ htop => le_antisymm le_top htop⟩
  refine ⟨P,?_⟩
  change ((⊤ : Subgroup (R.subgroupOf N)).map (R.subgroupOf N).subtype).map N.subtype = R
  rw [←MonoidHom.range_eq_map,range_subtype,map_subgroupOf_eq_of_le hRN]

omit [Finite G] in
private theorem raw_constrained_input_of_normalizes
    (H Mc L : Subgroup G) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hQne : (H ⊓ Mc).pCoreIn 2 ≠ ⊥)
    (hcontrol : ((H ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hnormalizer : H ⊓ normalizer ((H ⊓ Mc).pCoreIn 2 : Set G) = H ⊓ Mc)
    (hL : L ∈ Chapter1.cComponentsIn H)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hfit : generalizedFitting L = pCore 2 L) (hout : ¬L ≤ H ⊓ Mc)
    (hnL : (H ⊓ Mc).pCoreIn 2 ≤ normalizer (L : Set G)) :
    Input KnownSimple.IsKnownSimple H ((H ⊓ Mc).pCoreIn 2) (H ⊓ Mc) L := by
  let N := H ⊓ Mc
  let Q := N.pCoreIn 2
  have hQN : Q ≤ N := pCoreIn_le 2 N
  have hQH : Q ≤ H := hQN.trans inf_le_left
  have hNQ : N ≤ normalizer (Q : Set G) := N.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  let : (Q.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNQ
  have hclosure : (normalClosure (Q.subgroupOf N : Set N)).map N.subtype = Q := by
    rw [normalClosure_eq_self,map_subgroupOf_eq_of_le hQN]
  have hsy : Chapter1.IsSylowIn 2 Q
      ((normalClosure (Q.subgroupOf N : Set N)).map N.subtype) := by
    rw [hclosure]
    exact Chapter1.isSylowIn_iff.mpr ⟨isPGroup_pCoreIn 2 N,le_rfl,
      fun U _ hQU hUQ => le_antisymm hUQ hQU⟩
  exact ⟨⟨hH,hQH,inf_le_left,
    caseI_intrinsic_core_radical H N inf_le_left hQne hnormalizer,
    caseI_intrinsic_characteristic_control H Mc Q hQH hcontrol,hsy⟩,
    hL,hq,hfit,hout,hnL⟩

/-- Radical control on the literal constrained C-component gives either a
rank-one block or the actual star input and catalogue on that same component. -/
theorem raw_constrained_component_rankOne_or_star
    (H Mc L : Subgroup G) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hodd : pPrimeCore 2 H = ⊥)
    (hQne : (H ⊓ Mc).pCoreIn 2 ≠ ⊥)
    (hcontrol : ((H ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hnormalizer : H ⊓ normalizer ((H ⊓ Mc).pCoreIn 2 : Set G) = H ⊓ Mc)
    (hL : L ∈ Chapter1.cComponentsIn H)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hfit : generalizedFitting L = pCore 2 L) (hout : ¬L ≤ H ⊓ Mc) :
    ((∃ n : ℕ, IsL2EvenBlock L n) ∨ IsAlternatingBlock L 5) ∨
      ∃ hi : Input KnownSimple.IsKnownSimple H ((H ⊓ Mc).pCoreIn 2) (H ⊓ Mc) L,
        StarModels.Model (starImage L ((H ⊓ Mc).pCoreIn 2) L) ∧
          (coreToStar hi.normalizes).ker ≤ center (L ⧸ pCore 2 L) ∧
          (Nat.card (center (L ⧸ pCore 2 L)) = 1 ∨
            Nat.card (center (L ⧸ pCore 2 L)) = 3) := by
  let N := H ⊓ Mc
  let Q := N.pCoreIn 2
  let K := L.subgroupOf H
  let R := Q.subgroupOf H
  let N0 := N.subgroupOf H
  have hQH : Q ≤ H := (pCoreIn_le 2 N).trans inf_le_left
  have hRN : R ≤ N0 := fun _ hx => pCoreIn_le 2 N hx
  have hn : N0 ≤ normalizer (R : Set H) := by
    rw [←subgroupOf_normalizer_eq hQH]
    exact fun x hx => (N.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image N (pCore 2 N))) hx
  have hr := caseI_intrinsic_core_radical H N inf_le_left hQne hnormalizer
  have hcpu := caseI_intrinsic_characteristic_control H Mc Q hQH hcontrol
  have hsy := raw_normal_core_sylow_closure R N0 hRN hr.isPGroup hn
  let e : K ≃* L := subgroupOfEquivOfLe hL.1
  let : IsQuasisimple (L ⧸ pCore 2 L) := hq
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hf : generalizedFitting K = pCore 2 K := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,hfit]
  rcases ChapterC.Section04Constrained.sylow_intersection_or_normalizes_of_constrained
      hH R N0 K hr hcpu hsy hL.2 hodd hf with ⟨P,hP⟩ | hnorm
  · left
    have hPR : (P : Subgroup K).map K.subtype ≤ R := hP.le.trans inf_le_left
    have hb : IsChiZeroBlock L :=
      (constrained_component_chiZero_of_full_sylow hH R N0 K hr hcpu hL.2 hodd hf
        (fun hh => hout (fun l hl => hh (show (⟨l,hL.1 hl⟩ : H) ∈ K from hl)))
        P hPR).of_mulEquiv e
    rcases hb with hb | hb | hb
    · exact Or.inl hb
    · obtain ⟨f⟩ := hb.equiv_alternatingFour
      let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
      let : Group.IsSolvable L :=
        Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
      exact (hL.2.not_isSolvable
        (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
    · exact Or.inr hb
  · have hnL : Q ≤ normalizer (L : Set G) := by
      change Q.subgroupOf H ≤ normalizer (L.subgroupOf H : Set H) at hnorm
      rw [←subgroupOf_normalizer_eq hL.1] at hnorm
      intro x hx
      exact hnorm (show (⟨x,hQH hx⟩ : H) ∈ R from hx)
    have hi := raw_constrained_input_of_normalizes H Mc L hH hQne hcontrol
      hnormalizer hL hq hfit hout hnL
    exact Or.inr ⟨hi,star_model_from_source hi,coreToStar_ker_central_from_source hi,
      coreQuotient_center_card_from_source hi⟩

/-- The actual full quintic order-four partner source retains its literal
outside component and all earlier raw controls, with a genuine rank-one or
C.2.7 catalogue in its constrained branch. -/
theorem PreparedChosenModule.decomposable_five_partner_four_raw_star
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 4 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let MZ := G1 ⊓ Mc
      let Q1 := MZ.pCoreIn 2
      let S := (T : Subgroup G) ⊓ G1
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let W := ⁅V,R⁆
      let Y := (pResidual 2 MZ).map MZ.subtype
      letI := caseI_module_centralizer_normal (Z1 := Z1) h.normalized
      ∃ L : Subgroup G,
        Z1 ≤ thompsonFixed T V ∧ Nat.card Z1 = 4 ∧
        Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5 ∧
        MZ = centralizer (thompsonFixed T V : Set G) ∧
        pPrimeCore 2 G1 = ⊥ ∧ Chapter1.IsSylowIn 2 S G1 ∧
        (S.subgroupOf (T : Subgroup G)).Normal ∧
        (pResidual 2 (M ⊓ Mc ⊓ G1 : Subgroup G)).map (M ⊓ Mc ⊓ G1).subtype =
          (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
            (M ⊓ centralizer (V : Set G)).subtype ∧
        centralInvolutions T ⊓ V ≤ Z1 ⊔ W ∧
        Q1 ≠ ⊥ ∧ Q1.characteristicNormalizerClosure ≤ Mc ∧
        G1 ⊓ normalizer (Q1 : Set G) = MZ ∧
        (T : Subgroup G) ≤ normalizer (MZ : Set G) ∧
        (T : Subgroup G) ≤ normalizer (Q1 : Set G) ∧
        normalizer (Y : Set G) ≤ Mc ∧ Y ≤ centralizer (centralInvolutions T : Set G) ∧
        (∃ P : Sylow 2 G1, (P : Subgroup G1).map G1.subtype = S ∧
          ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses G1 P Mc z) ∧
        L ∈ Chapter1.cComponentsIn G1 ∧ ¬ L ≤ MZ ∧
        IsQuasisimple (L ⧸ pCore 2 L) ∧ L ∈ Chapter1.L G S ∧
        Chapter1.IsSylowIn 2 (S ⊓ L) L ∧ ¬ L ≤ M ∧
        R ⊔ W ≤ normalizer (L : Set G) ∧ ⁅L,W⁆ ≠ ⊥ ∧
        (IsComponent G1 (L.subgroupOf G1) ∨
          (generalizedFitting L = pCore 2 L ∧
            (((∃ n : ℕ, IsL2EvenBlock L n) ∨ IsAlternatingBlock L 5) ∨
              ∃ hi : Input KnownSimple.IsKnownSimple G1 Q1 MZ L,
                StarModels.Model (starImage L Q1 L) ∧
                  (coreToStar hi.normalizes).ker ≤ center (L ⧸ pCore 2 L) ∧
                  (Nat.card (center (L ⧸ pCore 2 L)) = 1 ∨
                    Nat.card (center (L ⧸ pCore 2 L)) = 3)))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
  let G1 := centralizer (Z1 : Set G)
  obtain ⟨L,hZ,hZcard,hcard,hMZ,ho,hSylG,hSn,hI,hseed,hQne,hcontrol,hn,
    hTn,hTQ,hresN,hYseed,h115,hLc,hout,hquasi,hloc,hSyl,houtM,hnL,hmove,hcases⟩ :=
    h.decomposable_five_partner_four_raw_component
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  refine ⟨L,hZ,hZcard,hcard,hMZ,ho,hSylG,hSn,hI,hseed,hQne,hcontrol,hn,
    hTn,hTQ,hresN,hYseed,h115,hLc,hout,hquasi,hloc,hSyl,houtM,hnL,hmove,?_⟩
  rcases hcases with hordinary | hfit
  · exact Or.inl hordinary
  · have hZne : Z1 ≠ ⊥ := (one_lt_card_iff_ne_bot Z1).mp (by rw [hZcard]; decide)
    have hH := caseI_centralizer_sqtk hG Z1 hZne
      ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
    exact Or.inr ⟨hfit,raw_constrained_component_rankOne_or_star G1 Mc L hH
      ho hQne hcontrol hn hLc hquasi hfit hout⟩

end CFSG.Quasithin.Chapter15.Section01
