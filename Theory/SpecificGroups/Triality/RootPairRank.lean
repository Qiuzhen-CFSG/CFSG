module
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ArmsReduction.Collection
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ArmsReduction.Weyl
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Four independent binary dimensions from two triality root groups

The cubic short-root group at position one commutes with the highest long
root group. Their product embeds the additive cubic field times the fixed
field in the genuine triality carrier: injectivity follows from the actual
arms-radical coordinates. This gives two-rank at least four times the field
degree, including the binary endpoint.

The Cartan containing-component application uses the endpoint to exclude
odd ternary sections, whose two-rank is at most three. No quotient-monotonicity
of two-rank or sharp five-times-degree formula is assumed.
Source: GLS3 sections 2.4--2.6, refs/KGroup/GLS3/chapter2.tex; the local
component comparison in Aschbacher--Smith 5.1.12--13, printed pp.635--638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.RootPairRank
open Parabolics RadicalCoordinates RadicalCoordinates.LeviCommutators
open EvenInvolutionGeometry.ArmsNormalization

private def rootPair (P : Parameters) (hp : P.prime = 2) :
    Multiplicative (ExtensionField P × fixedField P) →* Carrier P where
  toFun v := short P hp 1 v.toAdd.1 * long P hp 2 v.toAdd.2
  map_one' := by
    change short P hp 1 0 * long P hp 2 0 = 1
    rw [short_zero,long_zero,mul_one]
  map_mul' v w := by
    change short P hp 1 (v.toAdd.1 + w.toAdd.1) *
      long P hp 2 (v.toAdd.2 + w.toAdd.2) = _
    rw [short_add, long_add]
    exact (highest_commute_short P hp v.toAdd.2 1 w.toAdd.1).symm.mul_mul_mul_comm _ _

private theorem rootPair_coordinates (P : Parameters) (hp : P.prime = 2)
    (v : Multiplicative (ExtensionField P × fixedField P)) :
    rootPair P hp v = (armsCoordinates P hp (![v.toAdd.1,0],![0,0,v.toAdd.2])).val := by
  rw [armsCoordinates_factorization]
  simp only [rootPair, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, short_zero, long_zero,
    one_mul, mul_one]

private theorem rootPair_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (rootPair P hp) := by
  intro v w h
  rw [rootPair_coordinates,rootPair_coordinates] at h
  have hh := (armsCoordinates P hp).injective (Subtype.ext h)
  have h1 := congrArg (fun x => x.1 0) hh
  have h2 := congrArg (fun x => x.2 2) hh
  exact Prod.ext h1 h2

/-- The short cubic root and highest fixed root give an elementary subgroup
of order `2^(4*n)` in the actual standard carrier. -/
theorem twoRank_ge_four_mul (n : ℕ) (hn : 0 < n) :
    4 * n ≤ primeRank 2 (BinaryCarrier n hn) := by
  let P := binaryParameters n hn
  let : CharP (ExtensionField P) 2 := inferInstanceAs (CharP (ExtensionField P) P.prime)
  let : CharP (fixedField P) 2 := inferInstance
  apply primeRank_ge_of_elementary_embedding (f := rootPair P rfl)
  · intro v
    change 2 • v.toAdd = 0
    rw [two_nsmul]
    exact CharTwo.add_self_eq_zero v.toAdd
  · change Nat.card (ExtensionField P × fixedField P) = 2 ^ (4 * n)
    rw [Nat.card_prod,card_extensionField,card_fixedField]
    simp only [P,binaryParameters_q,← pow_mul,← pow_add]
    congr 1
    omega
  · exact rootPair_injective P rfl

end Triality.Standard.RootPairRank
