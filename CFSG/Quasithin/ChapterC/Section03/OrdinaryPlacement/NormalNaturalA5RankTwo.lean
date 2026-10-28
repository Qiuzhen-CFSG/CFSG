module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields
public import Theory.SpecificGroups.G2.MultiplierOrdinary
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.G2.FourBound
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

/-!
# Central-point restrictions on the ordinary rank-two rows

The original C.2.8 component has two-group center. The proved symplectic
and triality covering calculations make that center trivial. In the binary
G₂ family a nontrivial center forces field order four, and the exceptional
covering calculation bounds its order by two. These are direct applications
of concrete covering results, without the conditional global multiplier table.

Source: Aschbacher--Smith 12.7.5 and I.1.3, printed pp.840 and 407.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

private theorem ordinary_center_twoGroup
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) : IsPGroup 2 (center K) := by
  let := hK.2
  rw [IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)]
  exact pCore_isPGroup

omit [Finite G] in
/-- Every binary symplectic ordinary component in the simple range has
trivial center, so cannot contain the original nonidentity central point. -/
theorem ordinary_psp4_center_eq_bot
    (_h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n)) : center K = ⊥ := by
  let := hK.2
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 3 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
    omega
  exact center_eq_bot_of_centralQuotientEquiv
    (Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.universalProjection_ker_eq_bot hlarge)
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)

/-- Two-primary triality lifting excludes the entire source two-group center,
including the smallest genuine binary triality group. -/
theorem ordinary_triality_center_eq_bot
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) {n : ℕ} (hn : 0 < n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (K ⧸ center K)) :
    center K = ⊥ := by
  let := hK.2
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n hn).mp hm
  have htwo : ¬ 2 ∣ Nat.card
      (universalProjection (Triality.Standard.BinaryCarrier n hn)).ker := by
    by_cases hlarge : 2 ≤ n
    · exact Triality.Standard.CentralCovers.TwoPrimary.universal_not_two_dvd_kernel_of_two_le
        n hn hlarge
    · have hn1 : n = 1 := by omega
      subst n
      exact Triality.Standard.CentralCovers.TwoPrimary.smallField_universal_not_two_dvd_kernel
  have hd := (centralQuotientCover e).kernel_card_dvd_universal
  rw [centralQuotientCover_ker] at hd
  rcases (h.ordinary_center_twoGroup K hK).card_eq_or_dvd with hc | hc
  · exact Subgroup.card_eq_one.mp hc
  · exact (htwo (hc.trans hd)).elim

/-- A nontrivial center in the actual binary G₂ row forces the field-four
exception and the original full center has order at most two. -/
theorem ordinary_g2_nontrivial_center
    (_h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) (hz : center K ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At (K ⧸ center K) (2 ^ n)) :
    n = 2 ∧ Nat.card (center K) ≤ 2 := by
  let := hK.2
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hn2 : n = 2 := by
    by_contra hne
    have hlarge : 3 ≤ n := by omega
    exact hz (center_eq_bot_of_centralQuotientEquiv
      (Atlas.G2.MultiplierOrdinary.even_universalProjection_ker_eq_bot_of_card_pow hF hlarge) e)
  refine ⟨hn2, ?_⟩
  exact ChapterI.LieMultipliers.G2.fourSourceCenter_card_le_two_of_field e
    (by simpa only [hn2, show (2 : ℕ) ^ 2 = 4 from rfl] using hF)

end CFSG.Quasithin.ChapterC.HypothesisC28
