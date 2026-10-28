module
public import Theory.SpecificGroups.Monster.Construction.LocalEmbedding
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.QuadraticQuotient
public import Theory.GroupTheory.PrimeRankWitness

/-!
# The cocode elementary subgroup of the actual Monster carrier

The cocode coordinates form an elementary subgroup of order 4096 in the
source triality quotient. Its coordinate projection is a left inverse;
composing with the faithful local representation embeds it in the fixed
Griess automorphism group. The rank statement uses only finiteness of the
ambient carrier, as supplied by the finite-simple catalogue guard.
Source: Aschbacher, Sporadic Groups, §§14 and 27; Aschbacher–Smith A.2.12.
-/

noncomputable section
namespace Sporadic.Monster.TwoRank
open Construction Construction.TrialitySpin Atlas.Codes Atlas.Fischer

private def cocodeHom : Multiplicative Cocode →* Q1Image where
  toFun c := q1ImageMap (q1Param (loopOne, 0, c.toAdd))
  map_one' := by
    have h : q1Param (loopOne,0,0) = 1 := Subtype.ext q1Word_zero
    change q1ImageMap (q1Param (loopOne,0,0)) = 1
    rw [h, map_one]
  map_mul' c d := by
    simp only [← map_mul, q1Param_mul]
    simp [loopOne, q1WordProductSign, parkerSign]

private theorem cocodeHom_injective : Function.Injective cocodeHom := by
  intro c d h
  have hc := congrArg (fun g => (q1ImageCoordinates g).toAdd.cocode) h
  simpa [cocodeHom, q1Coordinates_param, q1WordCoordinates, loopOne] using hc

/-- The twelve-dimensional cocode embeds in the exact Griess carrier. -/
public def embedding : Multiplicative Cocode →* GriessGroup :=
  q1ToGriess.comp cocodeHom

public theorem embedding_injective : Function.Injective embedding :=
  q1ToGriess_faithful.comp cocodeHom_injective

/-- Every finite instance of the fixed Monster carrier has two-rank at least twelve. -/
public theorem twelve_le_twoRank [Finite GriessGroup] : 12 ≤ primeRank 2 GriessGroup := by
  apply primeRank_ge_of_elementary_embedding (f := embedding)
  · intro c
    apply Multiplicative.toAdd.injective
    change 2 • c.toAdd = 0
    rw [two_nsmul, ← two_smul Bit]
    exact zero_smul Bit _
  · rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative Cocode ≃ Cocode), cocode_card]
    norm_num
  · exact embedding_injective
end Sporadic.Monster.TwoRank
