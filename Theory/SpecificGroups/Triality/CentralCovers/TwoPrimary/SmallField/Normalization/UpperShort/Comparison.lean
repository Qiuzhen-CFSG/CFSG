module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.UpperShort.Transport
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.ShortRoots.Model


/-!
# Comparing the highest long and short commutators at q = 2

Conjugate the commuting pair consisting of long root 0 and short root 1 by
an inverse lift of short root 0, all at parameter one. The checked D₄ mixed
exchange gives the first image as the word long0 · long1 · short2 · short1.
The checked short exchange gives the second image as short1 · long2 · long1;
its highest-root correction is retained. Central-extension invariance compares
commutators of these words with the conjugated commuting pair. The prescribed
commuting pairs then remove the highest-root factor and identify the long
commutator with the inverse short commutator. The already proved square-one
property of the long commutator removes this inverse.

Thus no equality of lifts is inferred merely from equal projections. Only the
parameter-one instances of the two base exchanges are used, independently of
the remaining lifted trace and lower normalization calculations. The final
application identifies the entire normalized binary highest section.

Sources: GLS3 §2.4.5(b)(4–5), with the literal D₄ marking of `FoldedRoots`,
and §6.1 (`refs/KGroup/GLS3/chapter2.tex` and `chapter6.tex`); the triality
cover calculation used in Aschbacher–Smith I.1.3 (`refs/quasithin.pdf`, PDF p.418).
-/

public section

open Triality.Standard Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.CentralCovers.TwoPrimary
open Triality.Standard.CentralCovers.TwoPrimary.SmallField
open scoped commutatorElement
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField.UpperShort
noncomputable section

private theorem inverse_conjugate_of_exchange {E : Type*} [Group E]
    (a b q : E) (h : a*b = b*a*q) : a⁻¹*b*a = b*q⁻¹ := by
  calc
    a⁻¹*b*a = a⁻¹*(b*a*q)*q⁻¹ := by group
    _ = a⁻¹*(a*b)*q⁻¹ := by rw [h]
    _ = b*q⁻¹ := by group

private theorem compare_words {E : Type*} [Group E]
    (b c d e : E) (hb : b⁻¹ = b) (hc : c⁻¹ = c) (hd : d⁻¹ = d) (he : e⁻¹ = e)
    (hbc : Commute b c) (hce : Commute c e) (hde : Commute d e)
    (h : Commute (b*e*d*c) (c*e)) : ⁅b,e⁆ = ⁅d,c⁆ := by
  have hb_cancel (x : E) : b*(b*x) = x := by simpa only [hb] using inv_mul_cancel_left b x
  have hc_cancel (x : E) : c*(c*x) = x := by simpa only [hc] using inv_mul_cancel_left c x
  have hd_cancel (x : E) : d*(d*x) = x := by simpa only [hd] using inv_mul_cancel_left d x
  have hcc : c*c = 1 := by simpa only [hc] using inv_mul_cancel c
  have hee : e*e = 1 := by simpa only [he] using inv_mul_cancel e
  have hw : b*d = e*b*e*c*d*c := by
    calc
      b*d = b*e*d*c*(c*e) := by
        simp only [mul_assoc, hc_cancel, hde.symm.left_comm, hee, mul_one]
      _ = c*e*(b*e*d*c) := h.eq
      _ = e*b*e*c*d*c := by
        simp only [mul_assoc, hce.left_comm, hbc.symm.left_comm]
  have hw' : b*e*b*e = d*c*d*c := by
    calc
      b*e*b*e = b*(e*b*e*c*d*c)*(c*d*c) := by
        simp only [mul_assoc, hc_cancel, hd_cancel, hcc, mul_one]
      _ = b*(b*d)*(c*d*c) := by rw [hw]
      _ = d*c*d*c := by simp only [mul_assoc, hb_cancel]
  simpa only [commutatorElement_def, hb, hc, hd, he] using hw'

private theorem base_short_exchange_one (P : Parameters) (hp : P.prime = 2) :
    short P hp 0 1 * short P hp 1 1 =
      short P hp 1 1 * short P hp 0 1 * long P hp 1 1 * long P hp 2 1 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have ht : cubicTrace P 1 = 1 := cubicTrace_fixed P hp 1
  simpa only [map_one, mul_one, higherCoefficient, CharTwo.add_self_eq_zero,
    short_zero, ht] using short_zero_one_exchange P hp 1 1

private theorem base_mixed_exchange_one (P : Parameters) (hp : P.prime = 2) :
    short P hp 0 1 * long P hp 0 1 =
      long P hp 0 1 * short P hp 0 1 * short P hp 1 1 *
        short P hp 2 1 * long P hp 1 1 := by
  have hn : cubicNorm P 1 = 1 := by apply Subtype.ext; simp [cubicNorm]
  simpa only [Subfield.coe_one, map_one, mul_one, hn] using
    RootSections.ShortPolynomial.base_mixed P hp 1 1


local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one

private theorem short_inv_one {E : Type*} [Group E] {f : E →* G}
    (L : RootSections 1 Nat.zero_lt_one f) (i : Fin 3) :
    (L.shortRoot i (.ofAdd 1))⁻¹ = L.shortRoot i (.ofAdd 1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← map_mul]
  have h : (Multiplicative.ofAdd (1 : ExtensionField P)) * .ofAdd 1 = 1 := by
    apply Multiplicative.toAdd.injective
    exact CharTwo.add_self_eq_zero (1 : GaloisField 2 3)
  rw [h, map_one]

private theorem comparison {E : Type*} [Group E] (f : E →* G)
    (hk : f.ker ≤ Subgroup.center E) (L : RootSections 1 Nat.zero_lt_one f)
    (hcomm : CommutingPairs L) :
    longPairHighest L = ⁅L.shortRoot 1 (.ofAdd 1), L.shortRoot 2 (.ofAdd 1)⁆ := by
  let a := L.shortRoot 0 (.ofAdd 1)
  let b := L.longRoot 0 (.ofAdd 1)
  let c := L.shortRoot 1 (.ofAdd 1)
  let d := L.shortRoot 2 (.ofAdd 1)
  let e := L.longRoot 1 (.ofAdd 1)
  let z := L.longRoot 2 (.ofAdd 1)
  have hb : b⁻¹ = b := longRoot_inv f L 0 1
  have hc : c⁻¹ = c := short_inv_one L 1
  have hd : d⁻¹ = d := short_inv_one L 2
  have he : e⁻¹ = e := longRoot_inv f L 1 1
  have hz : z⁻¹ = z := longRoot_inv f L 2 1
  have hbc : Commute b c := by
    simpa [RootSections.factor, b, c] using
      hcomm 1 2 (0, ![1,0,0]) (![0,1,0], 0) (by decide) (by simp [interactingPair])
  have hce : Commute c e := by
    simpa [RootSections.factor, c, e] using
      hcomm 2 4 (![0,1,0], 0) (0, ![0,1,0]) (by decide) (by simp [interactingPair])
  have hde : Commute d e := by
    simpa [RootSections.factor, d, e] using
      hcomm 3 4 (![0,0,1], 0) (0, ![0,1,0]) (by decide) (by simp [interactingPair])
  have hbz : Commute b z := by
    simpa [RootSections.factor, b, z] using
      hcomm 1 5 (0, ![1,0,0]) (0, ![0,0,1]) (by decide) (by simp [interactingPair])
  have hcz : Commute c z := by
    simpa [RootSections.factor, c, z] using
      hcomm 2 5 (![0,1,0], 0) (0, ![0,0,1]) (by decide) (by simp [interactingPair])
  have hdz : Commute d z := by
    simpa [RootSections.factor, d, z] using
      hcomm 3 5 (![0,0,1], 0) (0, ![0,0,1]) (by decide) (by simp [interactingPair])
  have hez : Commute e z := by
    simpa [RootSections.factor, e, z] using
      hcomm 4 5 (0, ![0,1,0]) (0, ![0,0,1]) (by decide) (by simp [interactingPair])
  have hp1 : f (a⁻¹*b*a) = f (b*e*d*c) := by
    have hex : f a * f b = f b * f a * (f c * f d * f e) := by
      simpa only [a, b, c, d, e, L.project_short, L.project_long, mul_assoc] using
        base_mixed_exchange_one P rfl
    calc
      f (a⁻¹*b*a) = f (b*(c*d*e)⁻¹) := by
        simp only [map_mul, map_inv]
        exact inverse_conjugate_of_exchange (f a) (f b) _ hex
      _ = f (b*e*d*c) := by
        simp only [mul_inv_rev, he, hd, hc, mul_assoc]
  have hp2 : f (a⁻¹*c*a) = f (c*z*e) := by
    have hex : f a * f c = f c * f a * (f e * f z) := by
      simpa only [a, c, e, z, L.project_short, L.project_long, mul_assoc] using
        base_short_exchange_one P rfl
    calc
      f (a⁻¹*c*a) = f (c*(e*z)⁻¹) := by
        simp only [map_mul, map_inv]
        exact inverse_conjugate_of_exchange (f a) (f c) _ hex
      _ = f (c*z*e) := by simp only [mul_inv_rev, he, hz, mul_assoc]
  have hconj : ⁅a⁻¹*b*a, a⁻¹*c*a⁆ = 1 := by
    have h : Commute (a⁻¹*b*(a⁻¹)⁻¹) (a⁻¹*c*(a⁻¹)⁻¹) :=
      hbc.map (MulAut.conj a⁻¹)
    simpa only [inv_inv] using h.commutator_eq
  have hwz : ⁅b*e*d*c, c*z*e⁆ = 1 := by
    rw [← CentralExtension.commutator_eq_of_image_eq f hk hp1 hp2]
    exact hconj
  have hBz : Commute (b*e*d*c) z := ((hbz.mul_left hez).mul_left hdz).mul_left hcz
  have hw : Commute (b*e*d*c) (c*e) := by
    apply commutatorElement_eq_one_iff_commute.mp
    have hr : c*z*e = (c*e)*z := by rw [mul_assoc, hez.symm.eq, ← mul_assoc]
    rw [hr, commutatorElement_mul_right_eq_mul_conj, hBz.commutator_eq] at hwz
    simpa only [mul_one, mul_inv_cancel_right] using hwz
  have hc' : longPairHighest L = ⁅d,c⁆ := compare_words b c d e hb hc hd he hbc hce hde hw
  have hi : (longPairHighest L)⁻¹ = longPairHighest L :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using longPairHighest_square hk L hcomm)
  change longPairHighest L = ⁅c,d⁆
  calc
    longPairHighest L = (longPairHighest L)⁻¹ := hi.symm
    _ = ⁅d,c⁆⁻¹ := congrArg Inv.inv hc'
    _ = ⁅c,d⁆ := commutatorElement_inv d c

open PerfectCentralCovering
local notation "π" => universalProjection G
local notation "hf" => universalProjection_surjective G
local notation "hk" => universalProjection_ker_le_center G

/-- The two original highest commutators coincide in the universal central cover. -/
theorem universal_longPairHighest_eq_highestLift
    (hcomm : CommutingPairs universalRootSections) :
    longPairHighest universalRootSections = highestLift π hf hk :=
  comparison π hk universalRootSections hcomm

/-- Apply the comparison to the literal binary-section consumer, for every parameter. -/
theorem universal_normalized_long_two
    (hcomm : CommutingPairs universalRootSections) (t : fixedField P) :
    (longPairSections hk universalRootSections hcomm).longRoot 2 (.ofAdd t) =
      universalRootSections.longRoot 2 (.ofAdd t) :=
  normalized_long_two π hf hk hcomm (universal_longPairHighest_eq_highestLift hcomm) t

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField.UpperShort
