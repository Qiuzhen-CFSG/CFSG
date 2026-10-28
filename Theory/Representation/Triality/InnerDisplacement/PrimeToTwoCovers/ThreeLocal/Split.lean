module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Normalizer
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Order
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Split.PrimaryPair

/-!
# Split three-local configuration assembly

The actual cycle, inverter and their actions are constructed in Split.Normalizer.
Split.PrimaryPair constructs the primary torus generators using a square root
of the field norm. Together they give the complete configuration in the original
binary carrier. When three divides q−1, the proved split torus index supplies
the application to central-transfer geometry, with no additional premises.

Source: GLS3 §6.1, Theorem 6.1.4 and Tables 6.1.2–3; torus and Weyl
conventions from §§2.3–2.4.
-/

@[expose] public section
noncomputable section

namespace Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Split
open Standard Standard.Parabolics Standard.ConcreteBruhat
open PerfectCentralCovering.OddSylow

/-- All fields except the primary generator pair are constructed in the actual carrier. -/
def configurationOfPair (n : ℕ) (hn : 0 < n)
    (pair : TorusPair (primaryImage n hn)) : Configuration (torus (binaryParameters n hn)) where
  primary := primary n hn
  pair := pair
  cycle := cycle n hn
  inverter := inverter n hn
  cycle_order := cycle_order n hn
  cycle_outside := cycle_outside n hn
  normalizes := cycle_normalizes n hn
  inverts := inverter_inverts n hn
  fixes := inverter_commutes_cycle n hn

/-- Actual application to central-transfer geometry; the explicit remaining
premise is a pair of primary-torus generators with the stated conjugation equations. -/
theorem geometry_of_pair (n : ℕ) (hn : 0 < n) (hd : 3 ∣ 2 ^ n - 1)
    (pair : TorusPair (primaryImage n hn)) : Geometry 3 (BinaryCarrier n hn) :=
  (configurationOfPair n hn pair).geometry (nine_not_dvd_split_torus_index n hn hd)

/-- The split torus configuration, with all primary generators and Weyl actions
constructed in the original carrier. -/
def configuration (n : ℕ) (hn : 0 < n) : Configuration (torus (binaryParameters n hn)) :=
  configurationOfPair n hn (Classical.choice (nonempty_primary_pair n hn))

/-- Existence of the complete configuration for the existing split torus. -/
theorem nonempty_configuration (n : ℕ) (hn : 0 < n) :
    Nonempty (Configuration (torus (binaryParameters n hn))) :=
  ⟨configuration n hn⟩

/-- The split congruence branch supplies the actual central-transfer geometry
for every positive binary exponent and every three-adic valuation of q−1. -/
theorem geometry (n : ℕ) (hn : 0 < n) (hd : 3 ∣ 2 ^ n - 1) :
    Geometry 3 (BinaryCarrier n hn) :=
  (configuration n hn).geometry (nine_not_dvd_split_torus_index n hn hd)

end Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Split
