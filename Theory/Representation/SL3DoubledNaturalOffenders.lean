module

public import Theory.Representation.SL3DoubledNaturalOffenders.Centralizer
public import Theory.Representation.SL3DoubledNaturalOffenders.Displacement
public import Theory.Representation.SL3DoubledNaturalOffenders.NormalizerCoverage
public import Theory.Representation.SL3DoubledNaturalOffenders.TensorEstimate

/-!
# Offenders in the doubled-natural SL₃ normalizer

Over a finite field of positive odd binary degree, every elementary two-subgroup
of the literal binary normalizer that leaves the marked SL₃ component has rank
strictly less than its fixed codimension. Consequently every offender in that
normalizer lies in the component. Both copies use the same natural matrix,
and the result includes the field of order two.

The full binary commutant recovers the field and the multiplicity algebra.
Odd degree eliminates involutory field automorphisms, putting every elementary
normalizer actor in the actual SL₃ × SL₂ tensor subgroup. The tensor estimate
then compares the projection ranks with displacement; at maximal rank, the
common fixed space makes the inequality strict. This assembly discharges the
tensor-containment premise and supplies the intrinsic model estimate for the
doubled-natural branch of B.5.10(2).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.5.9(3) and B.5.10(2), printed pp.107–109.
-/

public section

namespace Representation.SL3DoubledNaturalOffenders
open BinaryOffender

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- An elementary subgroup of the full binary normalizer acting outside the
marked doubled-natural component has rank strictly below its fixed codimension. -/
theorem rank_lt_fixedCodim_of_le_normalizer {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (hpos : 0 < m) (hm : Odd m) {A : Subgroup (Ambient F)}
    (hA : IsElementaryTwo A) (hAN : A ≤ normalizer F) (hAC : ¬ A ≤ component F) :
    rank A < fixedCodim (action F) A := by
  exact rank_lt_fixedCodim_of_le_tensorSubgroup hF hpos hm hA
    (normalizer_elementary_le_tensorSubgroup hm hF A hA hAN) hAC

/-- Every offender in the full binary normalizer lies in the identically marked
natural SL₃ component, including in binary degree one. This is the intrinsic
localization used for the doubled-natural branch of B.5.10(2). -/
theorem offender_le_component_of_le_normalizer {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (hpos : 0 < m) (hm : Odd m) {A : Subgroup (Ambient F)}
    (hA : IsOffender (action F) A) (hAN : A ≤ normalizer F) : A ≤ component F := by
  by_contra hAC
  exact (not_lt_of_ge hA.2)
    (rank_lt_fixedCodim_of_le_normalizer hF hpos hm hA.1 hAN hAC)

end Representation.SL3DoubledNaturalOffenders
