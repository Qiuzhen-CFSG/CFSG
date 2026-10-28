module

public import Theory.GroupAction.NormalizerQuotientPointStabilizer
public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.Coordinates
public import Theory.GroupTheory.PResidual.PrimeSet
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The centralizer obstruction in the split dimension-four branch

The point stabilizer in the actual quotient N_G(A)/C_G(A) lifts into
C_G(z). Thus a {2,3}-centralizer excludes a PSL₃(2) subgroup fixing z.
For |A| < 35, orbit–stabilizer also excludes every A₇ subgroup of that
quotient: both 5 and 7 would have to divide an orbit of length at most |A|.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007. These are the terminal obstructions. Constructing
the compatible local images from the split block, and the involution-action
dichotomy leading to that block, remain separate mathematical obligations.
No splitting exclusion is asserted merely from an assumed image witness.
-/

open Subgroup

namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage

variable {G : Type*} [Group G] [Finite G]

private theorem prime_not_dvd_centralizer
    (A H : Subgroup G) (z : A)
    (hH : H = centralizer ({(z : G)} : Set G))
    (hpi : IsPiGroup twoThreePrimes H)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ∣ Nat.card (centralizer ({(z : G)} : Set G)) := by
  intro h
  rw [← hH] at h
  exact ((IsPiGroup_iff twoThreePrimes H).mp hpi ⟨p, hp⟩ h).elim hp2 hp3

/-- A PSL₃(2) subgroup fixing z in the literal quotient is incompatible
with the actual centralizer H being a {2,3}-group. -/
public theorem no_psl3Two_in_pointStabilizer
    (A H : Subgroup G) (z : A)
    (hH : H = centralizer ({(z : G)} : Set G))
    (hpi : IsPiGroup twoThreePrimes H)
    (f : Matrix.PSL3Two.PSL →* NormalizerAction.pointStabilizer A z) :
    ¬ Function.Injective f := by
  intro hf
  have hd := (Subgroup.card_dvd_of_injective f hf).trans
    (NormalizerAction.pointStabilizer_card_dvd A z)
  rw [Matrix.PSL3Two.card_PSL] at hd
  exact prime_not_dvd_centralizer A H z hH hpi 7 (by decide) (by decide) (by decide)
    ((by decide : 7 ∣ 168).trans hd)

/-- The source's E₁₆ action cannot contain A₇ if C_G(z) is a {2,3}-group.
This uses the faithful quotient action itself, without assuming a model
identification for its point stabilizer. -/
public theorem no_alternatingSeven_in_normalizerQuotient
    (A H : Subgroup G) (z : A)
    (hH : H = centralizer ({(z : G)} : Set G))
    (hpi : IsPiGroup twoThreePrimes H) (hA : Nat.card A < 35)
    (f : alternatingGroup (Fin 7) →* NormalizerAction.Star A) :
    ¬ Function.Injective f := by
  intro hf
  have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have h := NormalizerAction.prime_pair_le_card A f hf z 5 7
    (by decide) (by decide) (by decide)
    (by rw [hcard]; decide) (by rw [hcard]; decide)
    (prime_not_dvd_centralizer A H z hH hpi 5 (by decide) (by decide) (by decide))
    (prime_not_dvd_centralizer A H z hH hpi 7 (by decide) (by decide) (by decide))
  omega

/-- The compatible marked pair is already impossible. The proof uses
the checked words of orders five and seven in its generated coordinate
group, and lifts that group through the actual normalizer quotient.
The split-block calculation must still construct the marked pair. -/
public theorem no_markedLocalActions
    (A H P R : Subgroup G) (z : A)
    (hH : H = centralizer ({(z : G)} : Set G))
    (hpi : IsPiGroup twoThreePrimes H) :
    ¬ Nonempty (MarkedLocalActions A P R z) := by
  rintro ⟨d⟩
  have hcard : Nat.card A = 16 :=
    (Nat.card_congr d.coordinates.toEquiv).trans BinaryFourSplitPair.card_E
  have h := NormalizerAction.prime_pair_le_card A d.liftJoined
    d.liftJoined_injective z 5 7 (by decide) (by decide) (by decide)
    BinaryFourSplitPair.five_dvd_card_joined BinaryFourSplitPair.seven_dvd_card_joined
    (prime_not_dvd_centralizer A H z hH hpi 5 (by decide) (by decide) (by decide))
    (prime_not_dvd_centralizer A H z hH hpi 7 (by decide) (by decide) (by decide))
  omega

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage
