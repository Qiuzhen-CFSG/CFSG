module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat.Basic

/-!
# Positive correction roots and height

A strictly positive integral combination of positive F4 roots, when it is a
root, is positive and has height greater than either input. This is the
filtration used by the literal carrier collection proof.

Adapted from `SplitCoordinates.MatrixExchanges.Geometry`; only the positive
support is needed here. Source: GLS3 1.12.1(b), `refs/KGroup/GLS3/Chapter1.tex`.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup StandardRootSystem
open scoped BigOperators
namespace Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat.CollectionMatrices

/-- Roots in the strictly positive integral cone spanned by two roots. -/
def PositiveCone (r s t : F4Chevalley.Root) : Prop :=
  ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
    typeF4RootPairing.root t = p • typeF4RootPairing.root r + q • typeF4RootPairing.root s

/-- The first correction root in a Chevalley exchange. -/
theorem positiveCone_of_add {r s t : F4Chevalley.Root}
    (h : typeF4RootPairing.root t =
      typeF4RootPairing.root r + typeF4RootPairing.root s) : PositiveCone r s t :=
  ⟨1, 1, by decide, by decide, by simpa only [one_nsmul] using h⟩

/-- The second correction root when the first input is short. -/
theorem positiveCone_of_two_add {r s t : F4Chevalley.Root}
    (h : typeF4RootPairing.root t =
      (2 : ℕ) • typeF4RootPairing.root r + typeF4RootPairing.root s) : PositiveCone r s t :=
  ⟨2, 1, by decide, by decide, by simpa only [one_nsmul] using h⟩

/-- The second correction root when the second input is short. -/
theorem positiveCone_of_add_two {r s t : F4Chevalley.Root}
    (h : typeF4RootPairing.root t =
      typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root s) : PositiveCone r s t :=
  ⟨1, 2, by decide, by decide, by simpa only [one_nsmul] using h⟩

private lemma height_combination {r s t : F4Chevalley.Root} {p q : ℕ}
    (h : typeF4RootPairing.root t =
      p • typeF4RootPairing.root r + q • typeF4RootPairing.root s) :
    typeF4RootPairing_base.height t =
      p * typeF4RootPairing_base.height r + q * typeF4RootPairing_base.height s := by
  classical
  obtain ⟨f, _, _, hf⟩ := typeF4RootPairing_base.exists_root_eq_sum_int r
  obtain ⟨g, _, _, hg⟩ := typeF4RootPairing_base.exists_root_eq_sum_int s
  have ht : typeF4RootPairing.root t = ∑ j ∈ typeF4RootPairing_base.support,
      ((p : ℤ) * f j + (q : ℤ) * g j) • typeF4RootPairing.root j := by
    rw [h, hf, hg]
    simp only [Finset.smul_sum, add_smul, mul_smul, ← Finset.sum_add_distrib,
      Nat.cast_smul_eq_nsmul]
  rw [typeF4RootPairing_base.height_eq_sum ht,
    typeF4RootPairing_base.height_eq_sum hf,
    typeF4RootPairing_base.height_eq_sum hg]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- Natural height used by the collection algorithm. -/
def rootDegree (r : F4Chevalley.Root) : ℕ := typeF4RootPairing_base.height r |>.toNat

/-- Correction roots remain positive and lie strictly above both inputs. -/
theorem positiveCone_degree (r s : PositiveRoot)
    {t : F4Chevalley.Root} (ht : PositiveCone r.val s.val t) :
    typeF4RootPairing_base.IsPos t ∧
      max (rootDegree r.val) (rootDegree s.val) < rootDegree t := by
  obtain ⟨p, q, hp, hq, he⟩ := ht
  have hr := r.property
  have hs := s.property
  have hh := height_combination he
  have hpr : typeF4RootPairing_base.height r.val ≤
      (p : ℤ) * typeF4RootPairing_base.height r.val :=
    le_mul_of_one_le_left (le_of_lt hr) (by exact_mod_cast hp)
  have hqs : typeF4RootPairing_base.height s.val ≤
      (q : ℤ) * typeF4RootPairing_base.height s.val :=
    le_mul_of_one_le_left (le_of_lt hs) (by exact_mod_cast hq)
  have htpos : typeF4RootPairing_base.IsPos t := by
    change 0 < typeF4RootPairing_base.height t
    change 0 < typeF4RootPairing_base.height r.val at hr
    change 0 < typeF4RootPairing_base.height s.val at hs
    omega
  refine ⟨htpos, ?_⟩
  have hrt : (rootDegree r.val : ℤ) = typeF4RootPairing_base.height r.val :=
    Int.toNat_of_nonneg (le_of_lt hr)
  have hst : (rootDegree s.val : ℤ) = typeF4RootPairing_base.height s.val :=
    Int.toNat_of_nonneg (le_of_lt hs)
  have htt : (rootDegree t : ℤ) = typeF4RootPairing_base.height t :=
    Int.toNat_of_nonneg (le_of_lt htpos)
  change 0 < typeF4RootPairing_base.height r.val at hr
  change 0 < typeF4RootPairing_base.height s.val at hs
  omega

/-- An equality of actual root matrices with correction roots in their positive cone. -/
def MatrixExchange {K : Type*} [CommRing K] (r s : F4Chevalley.Root) (a b : K) : Prop :=
  ∃ correction : List (F4Chevalley.Root × K),
    (∀ z ∈ correction, PositiveCone r s z.1) ∧
      (F4Chevalley.rootCurve r a : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex K) *
          (F4Chevalley.rootCurve s b).val =
        (F4Chevalley.rootCurve s b).val * (F4Chevalley.rootCurve r a).val *
          (correction.map (fun z => (F4Chevalley.rootCurve z.1 z.2).val)).prod

end Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat.CollectionMatrices
