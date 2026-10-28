module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.ModelLifting
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.StarTransport
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.KernelCoordinates
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Containment
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import Theory.GroupTheory.GeneralizedFitting.ComponentInvolutionAction
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# Intrinsic recognition in the non-two-core branch of 15.4.22

The central four-group injects into the literal three-prime quotient. It
excludes the collapsed Goldschmidt triple and the first F.6.18 row by order.
The actual component action then selects A₆ from the established model sieve;
normality, the Sylow supplement and the S₆ quotient follow from the literal
quotient coordinates. The odd core is killed by the source inversion action
and the proved small-rank centralization theorem.

The full F.6.18 implication and genuine 1.1.5 component actions remain earlier
source inputs. No B.5 classifier or assumed A₆ supplement is used.
Source: Aschbacher–Smith 15.4.22, printed p.1165, and A.1.26/F.6.11–18.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors
open ComponentBranch FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure

namespace CFSG.Quasithin.Chapter15.Section04.SourceRecognition

universe u

variable {I : Type u} [Group I] [Finite I]

private theorem card_symmetric_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

/-- A source central four-group remains faithful in the actual star quotient.
F.6.11 supplies S intersect O_{3'} = O2, not an equality of the two cores. -/
theorem star_injective_on_four {A B : Subgroup I}
    (triple : ChapterF.IsGoldschmidtTriple A B) (S : Sylow 2 I)
    (hS : A ⊓ B = (S : Subgroup I)) (Z : Subgroup I)
    (hZS : Z ≤ (S : Subgroup I)) (hZQ : Z ⊓ pCore 2 I = ⊥) :
    Function.Injective ((QuotientGroup.mk' (pPrimeCore 3 I)).comp Z.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro z hz
  have hzN : (z : I) ∈ pPrimeCore 3 I := (QuotientGroup.eq_one_iff _).mp hz
  have hzQ : (z : I) ∈ pCore 2 I := by
    rw [← triple.intersection_inf_primeToThreeCore, hS]
    exact ⟨hZS z.property, hzN⟩
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hZQ ▸
    (show (z : I) ∈ Z ⊓ pCore 2 I from ⟨z.property, hzQ⟩))))

/-- The source four-group excludes both F.6.11 collapse and F.6.18 row (1).
This avoids an additional B.2.14/J(T) premise in the non-two-core branch. -/
theorem remaining_of_central_four {κ : GroupClass.{u}}
    (source618 : F618Universal κ) (hI : IsSQTK κ I)
    (A B : Subgroup I) (triple : ChapterF.IsGoldschmidtTriple A B)
    (S : Sylow 2 I) (hS : A ⊓ B = (S : Subgroup I))
    (Z : Subgroup I) (hZS : Z ≤ (S : Subgroup I))
    (hZcard : Nat.card Z = 4) (hZQ : Z ⊓ pCore 2 I = ⊥) :
    GoldschmidtAlternatives.Remaining (threePrimeImage A) (threePrimeImage B) := by
  let π := QuotientGroup.mk' (pPrimeCore 3 I)
  have hinj := star_injective_on_four triple S hS Z hZS hZQ
  have preserved : F611Preserved A B := by
    rcases (f611Conclusion_of_goldschmidt triple).alternatives with hp | hc
    · exact hp
    · obtain ⟨e⟩ := hc.symmetric_three
      have hd := Subgroup.card_dvd_of_injective
        (e.toMonoidHom.comp (π.comp Z.subtype)) (e.injective.comp hinj)
      rw [hZcard, card_symmetric_three] at hd
      norm_num at hd
  have hZimage : Nat.card (Z.map π) = 4 := by
    let e : Z ≃* Z.map π := MulEquiv.ofBijective (π.subgroupMap Z)
      ⟨fun _ _ he => hinj (congrArg Subtype.val he), π.subgroupMap_surjective Z⟩
    exact (Nat.card_congr e.toEquiv).symm.trans hZcard
  have hZle : Z.map π ≤ threePrimeImage A ⊓ threePrimeImage B := by
    rw [preserved.intersection, hS]
    exact map_mono hZS
  have hnot (U V : Subgroup (threePrimeQuotient I))
      (hUV : U ⊓ V = threePrimeImage A ⊓ threePrimeImage B) :
      ¬ GoldschmidtAlternatives.Case1 U V := by
    intro hc
    obtain ⟨e⟩ := hc.1
    have hd := card_dvd_of_le (hUV.symm ▸ hZle)
    rw [hZimage, Nat.card_congr e.toEquiv] at hd
    norm_num [GoldschmidtAlternatives.C] at hd
  rcases source618 hI (threePrimeImage A) (threePrimeImage B) preserved.triple with
    (hc | hr) | (hc | hr)
  · exact (hnot _ _ rfl hc).elim
  · exact Or.inl hr
  · exact (hnot _ _ (inf_comm _ _) hc).elim
  · exact Or.inr hr

/-- A.1.26 and the source inversion clause kill the full odd core. -/
theorem oddCore_eq_bot (hI : IsStronglyQuasithin I)
    (X V Z : Subgroup I) (hX : IsPPerfect 2 X)
    [IsElementaryAbelian 2 V] (hcomm : ⁅V, X⁆ = V)
    (hinter : Z ⊓ (center I ⊔ V) ≠ ⊥)
    (hinverts : ∀ z : Z, z ≠ 1 → ∀ x : pPrimeCore 2 I,
      (z : I) * (x : I) * (z : I)⁻¹ = (x : I)⁻¹) :
    pPrimeCore 2 I = ⊥ := by
  have hVC := ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hI X V hX hcomm
  have hfix : center I ⊔ V ≤ centralizer (pPrimeCore 2 I : Set I) :=
    sup_le (center_le_centralizer _) (commutator_eq_bot_iff_le_centralizer.mp hVC)
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinter
  let a : Z := ⟨z, z.property.1⟩
  have ha : a ≠ 1 := by
    intro he
    apply hz
    apply Subtype.ext
    change (z : I) = 1
    exact congrArg (fun w : Z => (w : I)) he
  apply le_bot_iff.mp
  intro x hx
  let b : pPrimeCore 2 I := ⟨x, hx⟩
  have hcommute : (z : I) * x = x * (z : I) := (hfix z.property.2 x hx).symm
  have hinv : x = x⁻¹ := by
    simpa only [a, b, hcommute, mul_assoc, mul_inv_cancel, mul_one] using hinverts a ha b
  have hpow : b ^ 2 = 1 := by
    apply Subtype.ext
    change x ^ 2 = 1
    rw [pow_two]
    exact (congrArg (fun y => y * x) hinv).trans (inv_mul_cancel x)
  have hd : orderOf b ∣ 1 := by
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_natCard b)
    simpa only [(pPrimeCore_coprime_card (p := 2) (G := I)).gcd_eq_one] using hd
  exact mem_bot.mpr (congrArg Subtype.val (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)))

/-- The output is constructed from F.6.18 and genuine 1.1.5 actions.
No component, supplement, or model identification is an input. -/
theorem intrinsic_recognition {κ : GroupClass.{u}}
    (source618 : F618Universal κ) (hI : IsSQTK κ I)
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
  have hrows := remaining_of_central_four source618 hI A B triple S hS Z hZS hZcard hZQ
  have h611 := f611Conclusion_of_goldschmidt triple
  obtain ⟨hstar, hsimple⟩ := ModelLifting.star_isComponent_and_simple L hL hodd h611.core_solvable
  have starModel := ModelLifting.intrinsicModel_of_remaining hstar hsimple
    triple.primeToThreeCore_quotient_twoCore_eq_bot hrows
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
