module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.Models
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear
public import Theory.GroupTheory.CComponent.CubicCenterRankNormal
public import Theory.GroupTheory.CComponent.OddRankNormal

/-!
# Normality of components with the original nonbinary quotient

The full natural quotient has center of order dividing three and has odd
prime rank at least two. Distinct component conjugates would force ambient
odd rank greater than two. At the cubic prime the intersection bound keeps
the full scalar center; at other primes the center is coprime to the actor.
This proves normality for any actual C-component with the covering quotient.

Source: Aschbacher--Smith A.3.8(3) and the contained-Fitting branch of
C.4.8, printed pp.46,153; applied to 4.4.6, printed p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The original SL₃ center is retained, including at field four. -/
theorem quotient_center_card_dvd_three : Nat.card (center (L ⧸ pCore 2 L)) ∣ 3 := by
  cases S.natural with
  | sl3 hm =>
    rw [Nat.card_congr (centerCongr hm.some.groupEquiv).toEquiv]
    exact Matrix.SL3.card_center_dvd_three S.field.Carrier
  | sp4 hm =>
    rw [Nat.card_congr (centerCongr hm.some.groupEquiv).toEquiv,
      Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot, card_bot]
    exact one_dvd _
  | g2 hm =>
    have hq : 2 < Nat.card S.field.Carrier := by
      rw [S.field.card_eq]
      have := Nat.pow_le_pow_right (n := 2) (by decide) S.nonbinary
      omega
    rw [Nat.card_congr (centerCongr hm.some.groupEquiv).toEquiv,
      Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hq, card_bot]
    exact one_dvd _

/-- An ambient component with the actual natural core quotient is normal. -/
theorem normal_of_natural_core_quotient {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (B : Subgroup H) (hB : B.IsCComponent)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L)) : B.Normal := by
  let := S.source.toHypothesis1221.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
  obtain ⟨p,hp,ho,hr⟩ := exists_odd_rank_two D S
  let : Fact p.Prime := ⟨hp⟩
  have hrB : 2 ≤ primeRank p (B ⧸ pCore 2 B) := by
    rwa [primeRank_congr p e]
  have hz : Nat.card (center (B ⧸ pCore 2 B)) ∣ 3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    exact quotient_center_card_dvd_three D S
  by_cases he : p = 3
  · subst p
    exact hB.normal_of_cubic_core_center_threeRank (Nat.le_of_dvd (by decide) hz)
      hrB (hH.stronglyQuasithin 3 Nat.prime_three (by decide))
  · have hc : Nat.Coprime p (Nat.card (center (B ⧸ pCore 2 B))) :=
      (hp.coprime_iff_not_dvd.mpr (fun hd =>
        he ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))).of_dvd_right hz
    exact hB.normal_of_coprime_core_center_primeRank ho hc hrB
      (hH.stronglyQuasithin p hp ho)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
