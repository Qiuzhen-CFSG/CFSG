module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.SmallQuotients
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.SmallModuleRanks.M24
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank
public import Theory.SpecificGroups.Held.TwoRank.Intrinsic
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix

/-!
# The sporadic obstruction in degree five reduces to J₄

The original moving subgroup embeds in the component central quotient with
order 256. The checked model orders exclude M₁₁, M₁₂, M₂₂, M₂₃, J₁ and J₂.
The intrinsic two-rank bounds exclude M₂₄, HS, He and Ru. Thus the genuine
Theorem C sporadic catalogue leaves only an actual isomorphism to J₄.
No new order or simplicity certification is needed.

`ModelReduction` applies this to the original nonsingular centralizer.
The J₄ local-action exclusion remains with qt-d-double-natural-centralizers.
Source: Aschbacher--Smith, 12.1.1 and A.2.3, printed pp.788 and32--33.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The sole remaining sporadic central quotient in degree five is the actual J₄ model. -/
theorem doubleNatural_five_adapted_component_sporadic_is_jankoFour
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ChapterA.Section02.IsTheoremCSporadicModel (K ⧸ center K) →
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK hm
  have hr := D.doubleNatural_adapted_component_centralQuotient_rank h B S w hw K hK
  rcases hm with ⟨name,hne,⟨e⟩⟩ | ⟨e⟩
  · let : Finite name.Carrier := Finite.of_equiv (K ⧸ center K) e.toEquiv
    rw [primeRank_equiv 2 e] at hr
    cases name with
    | j4 => exact ⟨e⟩
    | j3 => exact (hne rfl).elim
    | m11 =>
      have hu : primeRank 2 Sporadic.Mathieu.M11 ≤ 7 :=
        primeRank_le_of_prime_pow_not_dvd (by rw [Sporadic.Mathieu.m11_order]; decide)
      change 2*(5-1) ≤ primeRank 2 Sporadic.Mathieu.M11 at hr
      omega
    | m12 =>
      have hu : primeRank 2 Sporadic.Mathieu.M12 ≤ 7 :=
        primeRank_le_of_prime_pow_not_dvd (by rw [Sporadic.Mathieu.m12_order]; decide)
      change 2*(5-1) ≤ primeRank 2 Sporadic.Mathieu.M12 at hr
      omega
    | m22 =>
      have hu : primeRank 2 Sporadic.Mathieu.M22 ≤ 7 :=
        primeRank_le_of_prime_pow_not_dvd (by rw [Sporadic.Mathieu.m22_order]; decide)
      change 2*(5-1) ≤ primeRank 2 Sporadic.Mathieu.M22 at hr
      omega
    | m23 =>
      have hu : primeRank 2 Sporadic.Mathieu.M23 ≤ 7 :=
        primeRank_le_of_prime_pow_not_dvd (by rw [Sporadic.Mathieu.m23_order]; decide)
      change 2*(5-1) ≤ primeRank 2 Sporadic.Mathieu.M23 at hr
      omega
    | m24 =>
      have hu := Sporadic.Mathieu.m24_twoRank_le_six
      change 2*(5-1) ≤ primeRank 2 Sporadic.Mathieu.M24 at hr
      omega
    | j2 =>
      have hu : primeRank 2 Sporadic.LeechRelated.J2.Carrier ≤ 7 :=
        primeRank_le_of_prime_pow_not_dvd (by
          rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]; decide)
      change 2*(5-1) ≤ primeRank 2 Sporadic.LeechRelated.J2.Carrier at hr
      omega
    | hs =>
      have hu := Sporadic.LeechRelated.HS.twoRank_le_four
      change 2*(5-1) ≤ primeRank 2 Sporadic.LeechRelated.HS.Carrier at hr
      omega
    | he =>
      have hu := Held.primeRank_two_le_six
      change 2*(5-1) ≤ primeRank 2 Held.He at hr
      omega
    | ru =>
      have hu := Rudvalis.primeRank_le_six
      change 2*(5-1) ≤ primeRank 2 Rudvalis.Model at hr
      omega
  · obtain ⟨e⟩ := e
    rw [primeRank_equiv 2 e] at hr
    have hu : primeRank 2 Janko1.Model ≤ 7 :=
      primeRank_le_of_prime_pow_not_dvd (by rw [Janko1.card_model]; decide)
    omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
