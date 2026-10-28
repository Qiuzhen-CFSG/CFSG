module
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.ComponentRecognition.Intrinsic
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.FullSourceModels

/-!
# Corrected F-source classification in the actual 15.4.22 component branch

The original central four-group embeds in the literal three-prime quotient,
excluding F.6.11 collapse. Trivial local cores would make the first quotient
local S3, whose order is not divisible by four. The complete corrected source
alternatives therefore give a model of the same star component, including
both added rank-one field branches. The original central-kernel and involution
action arguments construct the actual A6 supplement and S6 quotient.
No legacy F618Universal or restricted local marks are instantiated.

Source: Aschbacher--Smith, F.6.11--18 and15.4.22, pp.306--310,1165.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors
open ComponentBranch FFBranch.ClassificationComparison
open ComponentBranch.AlternatingLocals.RawQuotient
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
namespace CFSG.Quasithin.Chapter15.Section04.SourceRecognition
universe u
variable {I : Type u} [Group I] [Finite I]

private theorem card_symmetric_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_perm]
  decide

/-- The corrected full source list models the actual simple star component. -/
theorem star_model_of_source_classification {κ : GroupClass.{u}}
    (sourceF : FSource.SourceClassificationInput κ) (hI : IsSQTK κ I)
    (A B : Subgroup I) (triple : ChapterF.IsGoldschmidtTriple A B)
    (S : Sylow 2 I) (hS : A ⊓ B = (S : Subgroup I))
    (Z : Subgroup I) (hZS : Z ≤ (S : Subgroup I))
    (hZcard : Nat.card Z = 4) (hZQ : Z ⊓ pCore 2 I = ⊥)
    (L : Subgroup I) (hL : IsComponent I L) (hodd : pPrimeCore 2 I = ⊥) :
    IntrinsicComponentModel (starImage L) := by
  let π := QuotientGroup.mk' (pPrimeCore 3 I)
  have hinj := star_injective_on_four triple S hS Z hZS hZQ
  have preserved : F611Preserved A B := by
    rcases (f611Conclusion_of_goldschmidt triple).alternatives with hp | hc
    · exact hp
    · obtain ⟨e⟩ := hc.symmetric_three
      have hd := Subgroup.card_dvd_of_injective
        (e.toMonoidHom.comp (π.comp Z.subtype)) (e.injective.comp hinj)
      rw [hZcard,card_symmetric_three] at hd
      norm_num at hd
  have hZimage : Nat.card (Z.map π) = 4 := by
    let e : Z ≃* Z.map π := MulEquiv.ofBijective (π.subgroupMap Z)
      ⟨fun _ _ he => hinj (congrArg Subtype.val he),π.subgroupMap_surjective Z⟩
    exact (Nat.card_congr e.toEquiv).symm.trans hZcard
  have hZle : Z.map π ≤ threePrimeImage A ⊓ threePrimeImage B := by
    rw [preserved.intersection,hS]
    exact map_mono hZS
  have hnone : ¬ (pCore 2 (threePrimeImage A) = ⊥ ∧ pCore 2 (threePrimeImage B) = ⊥) := by
    intro hc
    obtain ⟨eA⟩ := preserved.triple.quotient_left
    let e := QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hc.1.symm).trans eA)
    have hcard : Nat.card (threePrimeImage A) = 6 :=
      (Nat.card_congr e.toEquiv).trans card_symmetric_three
    have hd := card_dvd_of_le (hZle.trans inf_le_left)
    rw [hZimage,hcard] at hd
    norm_num at hd
  have hquot : ThreePrimeSQTKQuotient κ (I ⧸ pPrimeCore 3 I) :=
    { Cover := I, sqtk := hI, equiv := MulEquiv.refl _ }
  obtain ⟨_,_,hs⟩ := sourceF (I ⧸ pPrimeCore 3 I) (threePrimeImage A) (threePrimeImage B)
    preserved.triple hquot
  have h611 := f611Conclusion_of_goldschmidt triple
  obtain ⟨hcomp,hsimple⟩ := ModelLifting.star_isComponent_and_simple L hL hodd h611.core_solvable
  let := hsimple
  rcases hs with hs | hs
  · exact (ModelLifting.FullSource.component_model_of_source_alternative hcomp hs).resolve_left hnone
  · exact (ModelLifting.FullSource.component_model_of_source_alternative hcomp hs).resolve_left
      (fun hc => hnone hc.symm)

/-- The output is constructed from F.6.18 and genuine 1.1.5 actions.
No component, supplement, or model identification is an input. -/
theorem intrinsic_recognition_of_source_classification {κ : GroupClass.{u}}
    (sourceF : FSource.SourceClassificationInput κ) (hI : IsSQTK κ I)
    (A B : Subgroup I) (triple : ChapterF.IsGoldschmidtTriple A B)
    (S : Sylow 2 I) (hS : A ⊓ B = (S : Subgroup I))
    (Z : Subgroup I) [IsElementaryAbelian 2 Z]
    (hZS : Z ≤ (S : Subgroup I)) (hSZ : (S : Subgroup I) ≤ centralizer (Z : Set I))
    (hZcard : Nat.card Z = 4) (hZQ : Z ⊓ pCore 2 I = ⊥)
    (hodd : pPrimeCore 2 I = ⊥) (hne : generalizedFitting I ≠ pCore 2 I)
    (hc : ∀ z : Z, z ≠ 1 → HasCharacteristicTwo (centralizer ({(z : I)} : Set I)))
    (hm : ∀ L : Subgroup I, IsComponent I L → ∀ z : Z, z ≠ 1 →
      ∃ α : MulAut L, (∀ x : L, (α x : I) = (z : I) * (x : I) * (z : I)⁻¹) ∧
        ModelAction115 L α) :
    ∃ K : Subgroup I, ∃ hKn : K.Normal, let _ := hKn
      K ⊔ (S : Subgroup I) = ⊤ ∧ Nonempty (K ≃* alternatingGroup (Fin 6)) ∧
      IsPGroup 2 (I ⧸ K) ∧ Nonempty ((I ⧸ centralizer (K : Set I)) ≃* Equiv.Perm (Fin 6)) := by
  classical
  obtain ⟨L, hL⟩ := exists_component_of_generalizedFitting_ne hodd hne
  have hn : Z ≤ normalizer (L : Set I) := by
    intro z hz
    by_cases hz1 : z = 1
    · simpa only [hz1] using (normalizer (L : Set I)).one_mem
    obtain ⟨α, heval, _⟩ := hm L hL ⟨z, hz⟩ (fun he => hz1 (congrArg Subtype.val he))
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      simpa only [heval] using (α ⟨x, hx⟩).property
    · intro hx
      obtain ⟨y, hy⟩ := α.surjective ⟨z * x * z⁻¹, hx⟩
      have he := congrArg Subtype.val hy
      rw [heval] at he
      have hyx : (y : I) = x := by
        exact mul_left_cancel (mul_right_cancel he)
      exact hyx ▸ y.property
  have hfaith : Z ⊓ centralizer (L : Set I) = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    by_contra hz1
    have hz1' : z ≠ 1 := fun he => hz1 (mem_bot.mpr he)
    exact hL.not_centralizes_of_twoCore_centralizer z
      (hc ⟨z, hz.1⟩ (fun he => hz1' (congrArg Subtype.val he))) hz.2
  obtain ⟨action, _, heval⟩ := exists_fixedAction_of_component L Z hL S hn hfaith hSZ hc
  have hmodels (z : Z) (hz : z ≠ 1) : ModelAction115 L (action.action z) := by
    obtain ⟨α, hα, hmodel⟩ := hm L hL z hz
    have he : α = action.action z := by
      apply MulEquiv.ext
      intro x
      exact Subtype.ext ((hα x).trans (heval z x).symm)
    exact he ▸ hmodel
  have h611 := f611Conclusion_of_goldschmidt triple
  have starModel := star_model_of_source_classification sourceF hI A B triple S hS Z hZS
    hZcard hZQ L hL hodd
  have model := ModelLifting.intrinsicModel_of_star_model L hL hodd h611.core_solvable
    action hZcard hmodels starModel
  let : IsQuasisimple L := hL.2
  obtain ⟨⟨eL⟩, ⟨eS⟩⟩ := action.select_alternatingSix hZcard model
  obtain ⟨eSelected⟩ := selected_join_equiv_innerExtension hI.stronglyQuasithin
    L Z hL eL action.action heval
  let e := AlternatingLocals.RawQuotient.wholeQuotientEquiv hI.stronglyQuasithin
    L Z hL eL S hZS hSZ hZcard hfaith (eSelected.trans eS)
  let coordinates := AlternatingLocals.KernelCoordinates.ofGoldschmidtTriple triple hL eL e
  let hLn : L.Normal := coordinates.component_normal
  have hquot : IsPGroup 2 (I ⧸ L) := coordinates.quotient_component_isTwoGroup
  have hgen : L ⊔ (S : Subgroup I) = ⊤ := by
    simpa only [sup_comm] using S.sup_eq_top_of_quotient_isPGroup L hquot
  have hkernel := AlternatingLocals.RawQuotient.core_eq_centralizer hI.stronglyQuasithin L hL eL
  exact ⟨L, hLn, hgen, ⟨eL⟩, hquot,
    ⟨(QuotientGroup.quotientMulEquivOfEq hkernel.symm).trans e⟩⟩


end CFSG.Quasithin.Chapter15.Section04.SourceRecognition
