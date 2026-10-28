module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat.PositiveCollection.Commuting

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.Geometry

/-!
# Integral operator input for the B₂ root-block swap

For a positive long root r and short root s with inner product -1, put
c = r + s and d = r + 2s. The root-length bound proves that the r,c;
r,d; s,d; and c,d operators commute. Thus only the two nonzero brackets,
[S,R] = ±C and [S,C] = ±2D, remain to determine the B₂ exponential swap.

The two structures below state those integral operator premises explicitly.
They do not assert a root-curve identity or supply either nonzero bracket.
The finite-exponential calculation and the signed brackets can be proved
independently; their eventual assembly must discharge both obligations.

Adapted from the corresponding `ReeF4.Parabolics.RadicalCoordinates` proof,
with its finite-carrier import removed.

Source: the B₂ Chevalley calculation underlying Aschbacher–Smith
F.1.12(I)(5), `refs/quasithin.pdf`, printed p.263 (PDF p.274).
-/

@[expose] public section

namespace Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat.CollectionMatrices

open ReeF4 Theory.AlgebraicGroup StandardRootSystem
open scoped Matrix
noncomputable section

/-- The two nonzero integral B₂ brackets. The signs refer to the actual
canonical integral operators; they disappear only after specialization. -/
structure B2BracketRelations (r s c d : F4Chevalley.Root) : Prop where
  short_long : ∃ ε : ℤ, ε ^ 2 = 1 ∧
    F4Chevalley.integralOperators.rootOperator s * F4Chevalley.integralOperators.rootOperator r -
      F4Chevalley.integralOperators.rootOperator r * F4Chevalley.integralOperators.rootOperator s =
        ε • F4Chevalley.integralOperators.rootOperator c
  short_sum : ∃ δ : ℤ, δ ^ 2 = 1 ∧
    F4Chevalley.integralOperators.rootOperator s * F4Chevalley.integralOperators.rootOperator c -
      F4Chevalley.integralOperators.rootOperator c * F4Chevalley.integralOperators.rootOperator s =
        (2 * δ) • F4Chevalley.integralOperators.rootOperator d

/-- Integral operator data for the B₂ exponential calculation. These are
Lie brackets, not an assumed group swap relation. -/
structure IntegralB2Relations (r s c d : F4Chevalley.Root) : Prop
    extends B2BracketRelations r s c d where
  long_sum : Commute (F4Chevalley.integralOperators.rootOperator r)
    (F4Chevalley.integralOperators.rootOperator c)
  long_top : Commute (F4Chevalley.integralOperators.rootOperator r)
    (F4Chevalley.integralOperators.rootOperator d)
  short_top : Commute (F4Chevalley.integralOperators.rootOperator s)
    (F4Chevalley.integralOperators.rootOperator d)
  sum_top : Commute (F4Chevalley.integralOperators.rootOperator c)
    (F4Chevalley.integralOperators.rootOperator d)

private lemma absent_of_large_norm (x : Vec 4) (hx : 2 < dot x x) :
    x ≠ 0 ∧ x ∉ Set.range typeF4RootPairing.root := by
  constructor
  · intro h
    subst x
    norm_num [dot] at hx
  · rintro ⟨t, ht⟩
    have hb : dot t.val t.val ≤ 2 := by
      by_cases h : IsLongRoot t
      · rw [isLongRoot_norm t h]
      · rw [isShortRoot_norm t h]; norm_num
    rw [typeF4RootPairing_root] at ht
    rw [ht] at hb
    linarith

/-- All four remaining brackets in a positive B₂ block vanish geometrically.
Only the two signed nonzero brackets remain as explicit input. -/
theorem integralB2Relations_of_brackets (r s c d : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (hl : IsLongRoot r) (hshort : IsShortRoot s)
    (hdot : dot r.val s.val = -1)
    (hc : c.val = r.val + s.val)
    (hd : d.val = r.val + (2 : ℝ) • s.val)
    (hbracket : B2BracketRelations r s c d) : IntegralB2Relations r s c d := by
  have hcp : typeF4RootPairing_base.IsPos c := hr.add hs
    (by simpa only [typeF4RootPairing_root] using hc)
  have hdp : typeF4RootPairing_base.IsPos d := hcp.add hs (by
    simp only [typeF4RootPairing_root]
    rw [hd, hc, two_smul]
    abel)
  have hnorm (u v : ℝ) :
      dot (u • r.val + v • s.val) (u • r.val + v • s.val) =
        2 * u ^ 2 + v ^ 2 - 2 * u * v := by
    have he : dot s.val r.val = -1 := by simpa only [dot, mul_comm] using hdot
    change (u • r.val + v • s.val) ⬝ᵥ (u • r.val + v • s.val) = _
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    change u * (u * dot r.val r.val + v * dot s.val r.val) +
      v * (u * dot r.val s.val + v * dot s.val s.val) = _
    rw [isLongRoot_norm r hl, isShortRoot_norm s hshort, hdot, he]
    ring
  have hcomm (i j : F4Chevalley.Root)
      (hip : typeF4RootPairing_base.IsPos i) (hjp : typeF4RootPairing_base.IsPos j)
      (u v : ℝ) (heq : i.val + j.val = u • r.val + v • s.val)
      (hbound : 2 < 2 * u ^ 2 + v ^ 2 - 2 * u * v) :
      Commute (F4Chevalley.integralOperators.rootOperator i)
        (F4Chevalley.integralOperators.rootOperator j) := by
    have hlarge : 2 < dot (i.val + j.val) (i.val + j.val) := by
      rw [heq, hnorm]
      exact hbound
    obtain ⟨h0, hsum⟩ := absent_of_large_norm _ hlarge
    exact integralOperators_commute_of_no_sum i j hip hjp h0 hsum
  refine ⟨hbracket, ?_, ?_, ?_, ?_⟩
  · exact hcomm r c hr hcp 2 1 (by rw [hc]; module) (by norm_num)
  · exact hcomm r d hr hdp 2 2 (by rw [hd]; module) (by norm_num)
  · exact hcomm s d hs hdp 1 3 (by rw [hd]; module) (by norm_num)
  · exact hcomm c d hcp hdp 2 3 (by rw [hc, hd]; module) (by norm_num)

end
end Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat.CollectionMatrices
