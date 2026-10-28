module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.SourceSpan
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Ordering
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.ThompsonBranches
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# The original twelve outside-overgroup conclusions

The genuine 15.3.7 source supplies the residual image, normalizer, core,
uniqueness and both complete three-group alternatives. The residual seed
span follows from its action image and the original Sylow supplement.
These discharge the earlier inputs to the two choices in 15.3.10.

The natural plane geometry and 15.3.5 supply the Sylow, characteristic-two
and Thompson conclusions. A.1.26 is applied inside the actual outside
subgroup I to its actual commutator-generated elementary module; this
module's normalizer bound puts O(I) inside M∩I, forcing O(I)=1.
Every clause of 15.3.11 is constructed, including the literal star quotient.

The remaining preceding source data are the natural orthogonal action from
15.1.3 and the distinct ordering maximum with N_G(Baum(T))≤M from14.1.12.
Source: Aschbacher--Smith 15.3.10--11, printed pp.1123--1124.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
open ChapterA.Section05To06 LocalBranches
variable {G : Type*} [Group G] [Finite G]

private def elementaryCoordinates :
    ThreeAlternatives.ElementaryNine ≃* Multiplicative (Fin 2 → ZMod 3) where
  toFun x := Multiplicative.ofAdd ![Multiplicative.toAdd x.1,Multiplicative.toAdd x.2]
  invFun x := (Multiplicative.ofAdd (Multiplicative.toAdd x 0),
    Multiplicative.ofAdd (Multiplicative.toAdd x 1))
  left_inv x := rfl
  right_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl

omit [Finite G] in
/-- The full original alternatives expressed in the literal downstream quotient convention. -/
theorem earlier_three_alternatives_of_source (d : CharacteristicTwo.LocalData G)
    (h : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action) :
    QuotientTheta.EarlierThreeAlternatives d := by
  rcases h with ⟨hc,⟨e⟩,hr⟩ | ⟨⟨e⟩,hc,hcy,ht,hP⟩
  · exact Or.inl ⟨⟨e.trans elementaryCoordinates⟩,hc.symm,hr⟩
  · exact Or.inr ⟨⟨(HeisenbergPrime.isExtraspecial (p := 3) (by decide)).of_mulEquiv e.symm,
      (Nat.card_congr e.toEquiv).trans HeisenbergPrime.card,
      (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide)),
      hc.symm,ht⟩,hcy,hP⟩

private theorem oddCore_centralizes_chosen_module
    (d : CharacteristicTwo.LocalData G) (I : Subgroup G) (hI : I ∈ d.Hplus)
    (hQ : IsStronglyQuasithin I) (W : Subgroup G) (hWI : W ≤ I)
    [IsElementaryAbelian 2 W] (hcomm : W = ⁅W,d.Yplus⁆) :
    (pPrimeCore 2 I).map I.subtype ≤ centralizer (W : Set G) := by
  have hYI : d.Yplus ≤ I := le_sup_left.trans hI.1.2
  let X := d.Yplus.subgroupOf I
  let U := W.subgroupOf I
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWI
  have hY : IsPPerfect 2 d.Yplus := by
    rw [←chosen_residual_eq d.M d.Mc d.S d.V₁ d.Yplus d.choice]
    intro N hN hp
    have h := BenderSuzuki.External.hktPResidual_le N hN hp
    rw [twoResidualAmbient_has_top_twoResidual] at h
    exact top_unique h
  have hX : IsPPerfect 2 X := hY.of_surjective
    (subgroupOfEquivOfLe hYI).symm.toMonoidHom (subgroupOfEquivOfLe hYI).symm.surjective
  have hC : ⁅U,X⁆ = U := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWI,map_subgroupOf_eq_of_le hYI,hcomm.symm]
  have hc := ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hQ X U hX hC
  have hm := congrArg (Subgroup.map I.subtype) hc
  rw [map_commutator,map_subgroupOf_eq_of_le hWI,Subgroup.map_bot] at hm
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hm)

/-- All twelve clauses of 15.3.11 from the original preceding orthogonal source data. -/
theorem source_lemma_15_3_11
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hne : d.Mc ≠ d.M)
    (hBaum : normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G) ≤ d.M)
    (I : Subgroup G) (hI : I ∈ d.Hplus) : Conclusions d I := by
  obtain ⟨hi,_,_,hNY,huY,hcore,h7⟩ :=
    source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  have hspan := source_residual_seed_span hG d.T hempty d.action hM hu hmany hne
  have hNV : normalizer (d.V : Set G) = d.M :=
    (InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1).symm
  have hNS : normalizer (d.S : Set G) ≤ d.M := by
    have h := (source_lemma_15_3_6 d.T d.action hM hBaum 1).2.1
    exact h.1.trans h.2
  have h24 (X : Subgroup G) (hTX : (d.T : Subgroup G) ≤ X) (hXM : X ≤ d.M) :
      twoResidualAmbient X ≤ d.M ⊓ centralizer (d.V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X d.M := by
    exact (source_lemma_15_3_2_4 d.T d.action hM hTX hXM).imp id And.right
  obtain ⟨hSyl,hC,hsecond,hN,hlocal,hθ⟩ :=
    local_branches d I hI (earlier_three_alternatives_of_source d h7) hi hspan hcore huY
      hNV hNY.symm hNS h24
  have hindex := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hf := lemma_15_3_11_7_of_index_two d.T d.M d.S I d.sylow_le inf_le_left
    (le_sup_right.trans hI.1.2) hindex (hG.evenCharacteristic d.T d.M hM.1.1 d.sylow_le)
  obtain ⟨W,_,_,hWI,hW,hcomm,_,hNW,_,hact⟩ := chosen_action d I hI hi hspan hNV
  let : IsElementaryAbelian 2 W := hW
  have ho : pPrimeCore 2 I = ⊥ :=
    oddCore_eq_bot_of_centralizing d.M I W hf.1
      (oddCore_centralizes_chosen_module d I hI
        (outside_stronglyQuasithin hG.quasithin d.Yplus d.S d.M I hI) W hWI hcomm)
      (inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hNW))
  have h35 := source_lemma_15_3_5 d.T d.action hM 1
  have hTh := lemma_15_3_11_10_11 d I hI hSyl hC hN hlocal hθ
    (h35.imp id (fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩))
  refine {
    sylow := hSyl
    centralizer_le := hC
    second_choice := hsecond
    normalizer_eq := hN
    local_structure := hlocal
    theta_eq := hθ
    generalized_fitting := hf.2
    odd_core := ho
    action_normalizer := lemma_15_3_11_9_of_local_facts d.Z d.Yplus d.S d.M I hI hC hN hθ.symm hact
    thompson_alternative := hTh.1
    thompson_outside := hTh.2
    characteristic_exclusion := ?_ }
  intro L _ hcomm hLM C hChar hneC
  let : C.Characteristic := hChar
  exact lemma_15_3_11_12 d hindex h24 L hcomm hLM C hneC

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure
