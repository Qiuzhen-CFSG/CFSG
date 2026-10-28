module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.ModuleSize
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.OuterSections
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.BenderExclusion
public import Theory.Representation.BinaryPrimeDisplacement

/-!
# The remaining Mathieu odd-normalizer component rows

A faithful binary actor of order eleven moves at least ten dimensions.
The original orbit coordinates therefore give two-rank at least ten for V.
After residual placement, the component's odd center preserves this rank.
The proved Theorem B bounds remove all odd-characteristic, alternating and
finite sporadic rows except J₄, and also remove Sp₆(2). The nonzero module
in the perfect residual's two-core rules out the Bender rows.

The output keeps the original component, module, residual and actual simple
quotient section. Relative-rank-two characteristic-two groups and J₄ remain;
in particular the J₄/M₂₄ block has not been excluded. The Hall consumer
constructs this output only in the branch of genuine residual uniqueness.
Source: Aschbacher--Smith, 4.4.10--12 and the start of the proof of 4.4.3,
printed pp.621--623.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The order-eleven displacement bound in the literal chosen subgroup. -/
theorem sourceOrbit_mathieu_twoRank_ge_ten
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent) : 10 ≤ primeRank 2 V := by
  let : Finite D.orbitComponent :=
    Finite.of_surjective D.orbitComponentHom D.orbitComponentHom_surjective
  have h11 : 11 ∣ Nat.card D.orbitComponent :=
    (Chapter7.NormalizedSource.MathieuGeneration.mathieu_centralQuotient_eleven_dvd hm).trans
      (card_quotient_dvd_card _)
  let : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := D.orbitComponent) 11 h11
  let ρ := D.orbitRepresentation.comp D.orbitComponent.subtype
  have hf : Function.Injective ρ :=
    (subspaceImageRepresentation_injective _ _).comp D.orbitComponent.subtype_injective
  have hdim : 10 ≤ Module.finrank (ZMod 2) D.orbitSpace := by
    have ha := ten_le_fixedCodim_of_order_eleven ρ hf x hx
    have hb := fixedCodim_add_finrank ρ (zpowers x)
    omega
  have hcard : Nat.card V = 2 ^ Module.finrank (ZMod 2) D.orbitSpace := by
    calc
      Nat.card V = Nat.card D.sourceOrbit := congrArg (fun W : Subgroup G => Nat.card W) hV
      _ = Nat.card D.orbitSpace := (Nat.card_congr D.sourceOrbitCoordinates.toEquiv).symm
      _ = _ := by simpa only [Nat.card_zmod] using
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.orbitSpace)
  let := D.elementary
  let : IsElementaryAbelian 2 (⊤ : Subgroup V) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup V).subtype Subtype.val_injective
  exact hdim.trans (IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup V)
    (by simpa only [card_top] using hcard))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open ChapterA.Section02 ClassificationModels

/-- The rank filter retains J₄ alongside the relative-rank-two rows. -/
theorem rankTwo_or_jankoFour_of_mathieu_rank
    {Q : Type*} [Group Q] [Finite Q]
    (hm : IsTheoremBModel Q) (hr : 10 ≤ primeRank 2 Q)
    (hnb : ¬ IsBenderModel Q) :
    (∃ f : ℕ, IsRankTwoModel Q f) ∨ Nonempty (Q ≃* Janko4.Model) := by
  rcases hm.remaining_of_twoRank_ge_eight (by omega) with ho | hb | hrank | hsp | hj
  · exact (no_theoremB_odd_model_of_twoRank_ge_eight (by omega) ho).elim
  · exact (hnb hb).elim
  · exact .inl hrank
  · exfalso
    obtain ⟨F,_,_,hcard,⟨e⟩⟩ := hsp
    have hb : primeRank 2 Q ≤ 9 := by
      apply primeRank_le_of_prime_pow_not_dvd
      intro hd
      have hd' : 2 ^ (9 + 1) ∣ Nat.card (Theory.SpecificGroups.SymplecticSix.Sp F) := by
        have hdq := (center (Theory.SpecificGroups.SymplecticSix.Sp F)).card_quotient_dvd_card
        rw [Nat.card_congr e.toEquiv] at hd
        exact hd.trans hdq
      rw [Theory.SpecificGroups.SymplecticSix.card_sp_of_card_two hcard] at hd'
      norm_num at hd'
    omega
  · exact .inr hj

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open ClassificationModels

/-- The remaining source configuration, with an actual model for the same
component central quotient and the original residual still embedded in it. -/
@[expose] def MathieuComponentCase {G : Type*} [Group G]
    (L V A : Subgroup G) (S : Type*) [Group S] : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧
    ((∃ f : ℕ, IsRankTwoModel (K ⧸ center K) f) ∨
      Nonempty ((K ⧸ center K) ≃* Janko4.Model)) ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧
    ∃ U : Subgroup (K ⧸ center K), ∃ f : U →* S, Function.Surjective f

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Apply the rank filter and perfect-residual Bender exclusion to the
component containing the original Mathieu module. -/
theorem sourceOrbit_mathieu_component_rows
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hc : NormalComponentCase L V A (D.orbitComponent ⧸ center D.orbitComponent)) :
    MathieuComponentCase L V A (D.orbitComponent ⧸ center D.orbitComponent) := by
  obtain ⟨K,hK,hn,hKV,hout,hcore,hmodel,hv,hf,hcent,hrK,hsection⟩ := hc
  have hr := (D.sourceOrbit_mathieu_twoRank_ge_ten hV hm).trans hrK
  refine ⟨K,hK,hn,hKV,hout,hcore,?_,hv,hf,hcent,hr,hsection⟩
  apply rankTwo_or_jankoFour_of_mathieu_rank hmodel hr
  intro hb
  let N := normalizer (A : Set G)
  let F := oddActorResidual L A
  let J := K.map N.subtype
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  obtain ⟨_,he,hWF,_⟩ := chosen_oddActorResidual_cover h D A hAN hcomm ho hAV
  let e : J ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let z : (J ⧸ center J) ≃* (K ⧸ center K) := QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
  exact no_bender_of_residual_module J F V hf hWF D.ne_bot he (hb.of_mulEquiv z)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
