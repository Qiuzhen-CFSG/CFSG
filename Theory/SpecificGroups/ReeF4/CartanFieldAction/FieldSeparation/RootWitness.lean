module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.RootCurve
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.RootDuality.Negation

/-!
# Fixed end-root words for the Ree trace calculation

Pair the two positive end roots with parameters `t` and `t^(2^m)` and
multiply by the two negative end-root elements at parameter one. Both pairs
are fixed by the exceptional field twist: it swaps the two orthogonal roots
and applies their prescribed parameter powers. Their product is therefore an
actual element of the fixed group, with the displayed four-factor matrix.

This constructs the witnesses for the field-separation trace argument. It
does not yet calculate their traces. The construction includes `m = 0` in
the full fixed group and makes no assertion about the Tits simple carrier.

Source: the type VI root group in GLS3, Table 2.4, and the field/inner-diagonal
separation in Theorem 2.5.12(a) (`refs/KGroup/GLS3/chapter2.tex`), used in
Aschbacher–Smith, A.3.15(5) and Proposition 1.3.4, printed pp.50–51,511
(`refs/quasithin.pdf`).
-/

@[expose] public section

namespace ReeF4.Cartan.FieldSeparation
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Parabolics.OuterLocal.SuzukiCommutators Parabolics
noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {m : ℕ}
noncomputable section

private theorem negative_end_commute (m : ℕ) :
    Commute (rootGeneratorInGroup m (-typeF4SimpleRootIndex 0) 1)
      (rootGeneratorInGroup m (-typeF4SimpleRootIndex 3) 1) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, rootGeneratorInGroup_coe, F4Chevalley.rootCurve,
    F4Chevalley.integralOperators, ← typeF4RootPairing_baseEquiv_val,
    rootCurveUnit_neg_simple]
  have hn : typeF4RootPairing_baseEquiv 0 ≠ typeF4RootPairing_baseEquiv 3 := by
    intro h
    have he := typeF4RootPairing_baseEquiv.injective h
    exact (by decide : (0 : Fin 4) ≠ 3) he
  have hc : typeF4RootPairing_base.cartanMatrix
      (typeF4RootPairing_baseEquiv 3) (typeF4RootPairing_baseEquiv 0) = 0 := by
    rw [typeF4RootPairing_base_cartan_apply]
    rfl
  exact congrArg Subtype.val
    (commute_negative_negative_of_cartan_eq_zero
      (typeF4RootPairing_baseEquiv 0) (typeF4RootPairing_baseEquiv 3) hn hc
      (1 : CoefficientField m) 1).eq

/-- The two commuting negative end-root elements at parameter one. -/
def negativeEndWord (m : ℕ) : SplitGroup m :=
  rootGeneratorInGroup m (-typeF4SimpleRootIndex 0) 1 *
    rootGeneratorInGroup m (-typeF4SimpleRootIndex 3) 1

/-- The exceptional field twist fixes the negative pair. -/
theorem negativeEndWord_fixed (d : LocalBlockInput m) :
    d.twist (negativeEndWord m) = negativeEndWord m := by
  have hf (r : F4Chevalley.Root) : exceptionalParameter r (1 : CoefficientField m) = 1 := by
    by_cases hr : IsLongRoot r
    · exact exceptionalParameter_of_long hr 1
    · rw [exceptionalParameter_of_short hr, one_pow]
  simp only [negativeEndWord, map_mul, d.twist_root, one_pow, hf,
    exceptionalRootPermutation_neg_simple]
  exact (negative_end_commute m).eq.symm

/-- An actual fixed-group element with a variable positive root parameter. -/
def traceWitness (d : LocalBlockInput m) (t : CoefficientField m) : d.fixedGroup :=
  ⟨endRootWord m t * negativeEndWord m,
    by rw [d.mem_fixedGroup, map_mul, endRootWord_fixed d, negativeEndWord_fixed d]⟩

/-- The exact four-root matrix whose trace is needed for field separation. -/
theorem traceWitness_matrix (d : LocalBlockInput m) (t : CoefficientField m) :
    (traceWitness d t).val.val =
      F4Chevalley.rootCurve (typeF4SimpleRootIndex 0) t *
      F4Chevalley.rootCurve (typeF4SimpleRootIndex 3)
        (t ^ (2 ^ m)) *
      (F4Chevalley.rootCurve (-typeF4SimpleRootIndex 0) (1 : CoefficientField m) *
      F4Chevalley.rootCurve (-typeF4SimpleRootIndex 3) (1 : CoefficientField m)) := by
  have h0 : IsLongRoot (typeF4SimpleRootIndex 0) :=
    (typeF4SimpleRootIndex_mem_pair_iff 0).mpr (by decide)
  have he : rootFieldEnd m (typeF4SimpleRootIndex 0) t = t ^ (2 ^ m) := by
    rw [rootFieldEnd_apply, exceptionalParameter_of_long h0]
  simp only [traceWitness, endRootWord, negativeEndWord, Subgroup.coe_mul,
    rootGeneratorInGroup_coe, he]
end
end ReeF4.Cartan.FieldSeparation
