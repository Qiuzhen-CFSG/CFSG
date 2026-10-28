module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132.Preparation
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Classification.Models

/-!
# Selecting the C.1.32 blocks in original 13.6.22

The original nonlinear small plus quotient has central quotient A₆ or
G₂(2)′. Compare all five C.1.32 outcomes with that same quotient. Sp₄(4)
has the wrong order. The upper unipotent subgroup of PSL₃(2ⁿ) forces
n=1, whose order 168 also differs from both central quotients. Thus only
the A₆, G₂(2) and covered-A₆ blocks remain, each contradicted by its
proved original marked exclusion.

The only extra input is the universal small C.1.32 implication, owned by
`qt-e-ms-small-ranktwo`. No C.1.34 hypothesis is needed for these rows.
Source: Aschbacher--Smith C.1.32 and 13.6.22, pp.135--136 and 932.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G]

private noncomputable def centerCongrQuotient {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro x hx
      exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)

private theorem nonlinear_central_card (K : Subgroup G)
    (h : Nonempty ((K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((K ⧸ centralPreimage (pCore 2 K)) ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    Nat.card (K ⧸ centralPreimage (pCore 2 K)) = 360 ∨
    Nat.card (K ⧸ centralPreimage (pCore 2 K)) = 6048 := by
  rcases h with h | h <;> obtain ⟨e⟩ := h
  · left
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  · right
    exact (Nat.card_congr e.toEquiv).trans
      (Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp))

private theorem not_sp4Four_of_central_card (K : Subgroup G)
    (hcard : Nat.card (K ⧸ centralPreimage (pCore 2 K)) = 360 ∨
      Nat.card (K ⧸ centralPreimage (pCore 2 K)) = 6048) : ¬ IsSp4FourBlock K := by
  rintro ⟨_, F, _, _, hF, rho, ⟨model⟩, _⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (f := 2) hF
  let e := ((centralPreimageQuotientEquiv (pCore 2 K)).trans
    (centerCongrQuotient model.quotientIso)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot).trans
          QuotientGroup.quotientBot)
  have he : Nat.card (K ⧸ centralPreimage (pCore 2 K)) = 979200 := by
    rw [Nat.card_congr e.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp, hF]
    norm_num
  rcases hcard with h | h <;> omega

private theorem not_linearThree_of_central_card (K : Subgroup G)
    (hcard : Nat.card (K ⧸ centralPreimage (pCore 2 K)) = 360 ∨
      Nat.card (K ⧸ centralPreimage (pCore 2 K)) = 6048)
    (n : ℕ) (hn : 1 ≤ n) (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) F) : False := by
  let f := (centralPreimageQuotientEquiv (pCore 2 K)).trans (centerCongrQuotient e)
  have hd : 2 ^ (n * 3) ∣ Nat.card (K ⧸ centralPreimage (pCore 2 K)) := by
    rw [Nat.card_congr f.toEquiv, pow_mul, ← hF,
      ← Matrix.PSL3.LinearThree.card_unipotent F]
    exact card_subgroup_dvd_card (Matrix.PSL3.LinearThree.unipotent F)
  have hn1 : n = 1 := by
    by_contra h
    have h64 : 64 ∣ Nat.card (K ⧸ centralPreimage (pCore 2 K)) :=
      (pow_dvd_pow 2 (show 6 ≤ n * 3 by omega)).trans hd
    rcases hcard with hc | hc <;> rw [hc] at h64 <;> norm_num at h64
  let := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [hn1, pow_one, Nat.card_eq_fintype_card] using hF)).symm
  let e₂ := e.trans (Atlas.fieldEquivSL 3 ef)
  let e₃ := ((centralPreimageQuotientEquiv (pCore 2 K)).trans
    (centerCongrQuotient e₂)).trans
      ((QuotientGroup.quotientMulEquivOfEq Matrix.PSL3Two.center_eq_bot).trans
        QuotientGroup.quotientBot)
  have he : Nat.card (K ⧸ centralPreimage (pCore 2 K)) = 168 :=
    (Nat.card_congr e₃.toEquiv).trans Matrix.PSL3Two.card_SL
  rcases hcard with hc | hc <;> omega

/-- Compare all five C.1.32 outcomes, preserving the actual block actions.
Neither discarded group family is excluded by a tag or an extra premise. -/
theorem blocks_of_rankTwoAlternatives (K R : Subgroup G)
    (hcentral : Nonempty ((K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((K ⧸ centralPreimage (pCore 2 K)) ≃* commutator (Atlas.G2.Model (ZMod 2))))
    (h : RankTwoAlternatives K R) :
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.IsG2TwoBlock K ∨ IsAlternatingBlock K 6 ∨ IsExceptionalAhat6Block K := by
  have hcard := nonlinear_central_card K hcentral
  rcases h with h | h | h | h | ⟨n,hn,F,hfield,hfinite,hF,⟨e⟩⟩
  · exact Or.inl h.2
  · exact Or.inr (Or.inl h.2)
  · exact (not_sp4Four_of_central_card K hcard h.2).elim
  · exact Or.inr (Or.inr h.2)
  · exact (not_linearThree_of_central_card K hcard n hn F hF e).elim

variable [Finite G] {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The original nonlinear small quotient exclusions, conditional only on
the genuine universal C.1.32 input and the earlier Chapter 13 sources. -/
theorem not_nonlinear_plus_original_source_of_rankTwo
    (rankTwo : ∀ (J : Type u) [Group J] [Finite J] (B R : Subgroup J),
      SmallMSPair KnownSimple.IsKnownSimple B R → RankTwoAlternatives B R)
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G))
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      RankTwo.LocalApplication.SourceHypothesis S I →
        omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G)) :
    ¬ NonlinearSmallQuotient (plusImage K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K) := by
  intro hmodel
  obtain ⟨hms,hcentral⟩ := smallMSPair_original_source d V₃ earlier standing hm hfusion
    h1332 h63 hK hL hz hmodel
  have hblocks := blocks_of_rankTwoAlternatives K _ hcentral (rankTwo G K _ hms)
  obtain ⟨hb,hc⟩ := not_binary_or_coveredSix_original_source d V₃ earlier standing hm
    hfusion hform hfailure h1332 h63 hK hL hz hmodel.reduced
  rcases hblocks with h | h | h
  · exact hb (.g2 h)
  · exact hb (.alternating h)
  · exact hc h

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132
