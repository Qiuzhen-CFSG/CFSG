module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.Coefficients
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.SylowReduction
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.UnipotentCocycle
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.Twist
public import Theory.SpecificGroups.Triality.BinaryCenter
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Normalization of triality field involutions

For an involution written as inner times coefficient, squaring the expression
and separating coefficient from inner automorphisms proves that the supplied
coefficient itself is involutory. Non-innerness makes it nontrivial. At n = 2m,
the scalar uniqueness theorem therefore identifies it with Frobenius^(3m).
Centerlessness of the genuine carrier makes the remaining inner factor g
satisfy g * sigma(g) = 1.

A solution g = h⁻¹ * sigma(h) gives the required intertwiner by conjugation
with h. The proved positive-root filtration and quadratic trace calculation,
order-three descent, and Sylow reduction supply such a solution in the genuine
carrier. `normalize_inner_coefficient` assembles these results with no remaining
cocycle or normalization premise, including m = 1. The earlier conditional
interfaces remain available. Simplicity, perfectness and global automorphism
coverage are not needed for normalization of the supplied expression.

Sources: Aschbacher–Smith, Notation 16.1.3 and Lemma 16.1.4(4), printed p.1171,
`refs/quasithin.pdf`; GLS3 §2.1 and Definition 2.5.13 / Proposition 2.5.17,
`refs/KGroup/GLS3/chapter2.tex`. The carrier and coefficient maps are those of
StandardModel, and all inner factors live in its actual central quotient.
-/

public section
noncomputable section
namespace Triality.Standard.EvenField.NormalForm
open OuterOdd

private theorem inner_mul_square {G : Type*} [Group G] (g : G) (c : MulAut G) :
    (MulAut.conj g * c)^2 = MulAut.conj (g * c g) * c^2 := by
  ext x
  change g * c (g * c x * g⁻¹) * g⁻¹ =
    (g * c g) * c (c x) * (g * c g)⁻¹
  simp only [map_mul, map_inv]
  group

/-- The coefficient in an actual inner–coefficient involution is itself a
nontrivial involution; this is derived, not imposed on the supplied expression. -/
theorem coefficient_involution_of_inner_coefficient
    (n : ℕ) (hn : 0 < n) (a : MulAut (BinaryCarrier n hn))
    (ha : a^2 = 1) (houter : a ∉ MulAut.innerSubgroup (BinaryCarrier n hn))
    (g : BinaryCarrier n hn) (e : CoefficientAut (binaryParameters n hn))
    (hform : a = MulAut.conj g * coefficientAction (binaryParameters n hn) e) :
    e^2 = 1 ∧ e ≠ 1 := by
  let c := coefficientAction (binaryParameters n hn) e
  have hs : MulAut.conj (g * c g) * c^2 = 1 :=
    (inner_mul_square g c).symm.trans ((congrArg (fun t => t^2) hform).symm.trans ha)
  have hc : coefficientAction (binaryParameters n hn) (e^2) =
      MulAut.conj ((g * c g)⁻¹) := by
    rw [map_pow, map_inv]
    exact eq_inv_of_mul_eq_one_right hs
  refine ⟨coefficient_eq_one_of_inner n hn (e^2) _ hc, ?_⟩
  intro he
  apply houter
  rw [hform, he, map_one, mul_one]
  exact ⟨g, rfl⟩

/-- Scalar uniqueness and centerlessness give the precise canonical cocycle
whose solution is required by the field-normalization consumer. -/
theorem canonical_coefficient_and_cocycle
    (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (a : MulAut (BinaryCarrier n hn))
    (ha : a^2 = 1) (houter : a ∉ MulAut.innerSubgroup (BinaryCarrier n hn))
    (g : BinaryCarrier n hn) (e : CoefficientAut (binaryParameters n hn))
    (hform : a = MulAut.conj g * coefficientAction (binaryParameters n hn) e) :
    e = coefficientFrobenius n hn (3*m) ∧
      g * coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) g = 1 := by
  obtain ⟨he, hne⟩ := coefficient_involution_of_inner_coefficient n hn a ha houter g e hform
  have heq := coefficient_involution_eq n hn m hm hnm e he hne
  refine ⟨heq, ?_⟩
  have hs := inner_mul_square g (coefficientAction (binaryParameters n hn) e)
  rw [← hform, ha, ← map_pow, he, map_one, mul_one] at hs
  apply MulAut.conj_injective_of_center_eq_bot (binaryCarrier_center_eq_bot n hn)
  rw [map_one, ← heq]
  exact hs.symm

/-- Conditional normalization on the literal carrier. The explicit premise is
nonabelian Lang solvability for the canonical scalar involution, with the
orientation g = h⁻¹ * sigma(h); conjugation by h is then the intertwiner. -/
theorem normalize_of_cocycle_solutions
    (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (hcocycle : ∀ g : BinaryCarrier n hn,
      g * coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) g = 1 →
      ∃ h : BinaryCarrier n hn,
        g = h⁻¹ * coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) h)
    (a : MulAut (BinaryCarrier n hn))
    (ha : a^2 = 1) (houter : a ∉ MulAut.innerSubgroup (BinaryCarrier n hn))
    (g : BinaryCarrier n hn) (e : CoefficientAut (binaryParameters n hn))
    (hform : a = MulAut.conj g * coefficientAction (binaryParameters n hn) e) :
    ∃ b : MulAut (BinaryCarrier n hn), ∀ x, b (a x) =
      coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) (b x) := by
  obtain ⟨heq, hg⟩ := canonical_coefficient_and_cocycle n hn m hm hnm a ha houter g e hform
  obtain ⟨h, hh⟩ := hcocycle g hg
  refine ⟨MulAut.conj h, ?_⟩
  intro x
  rw [hform, heq]
  change h * (g * coefficientAction (binaryParameters n hn)
      (coefficientFrobenius n hn (3*m)) x * g⁻¹) * h⁻¹ = _
  rw [hh]
  simp only [MulAut.conj_apply, map_mul, map_inv]
  group

/-- The explicit model input is restricted to the original positive subgroup;
the odd-index coset argument discharges global cocycle solvability. -/
theorem normalize_of_unipotent_cocycle_solutions
    (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (hlocal : ∀ u : BinaryCarrier n hn, u ∈ Parabolics.unipotent (binaryParameters n hn) →
      u * coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) u = 1 →
      ∃ v : BinaryCarrier n hn, v ∈ Parabolics.unipotent (binaryParameters n hn) ∧
        u = v⁻¹ * coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) v)
    (a : MulAut (BinaryCarrier n hn))
    (ha : a^2 = 1) (houter : a ∉ MulAut.innerSubgroup (BinaryCarrier n hn))
    (g : BinaryCarrier n hn) (e : CoefficientAut (binaryParameters n hn))
    (hform : a = MulAut.conj g * coefficientAction (binaryParameters n hn) e) :
    ∃ b : MulAut (BinaryCarrier n hn), ∀ x, b (a x) =
      coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) (b x) :=
  normalize_of_cocycle_solutions n hn m hm hnm
    (canonical_cocycle_solutions_of_unipotent n hn m hm hnm hlocal) a ha houter g e hform

/-- Every non-inner involution with an actual inner–coefficient expression is
conjugate to the canonical field involution. The coefficient and the cocycle
equation follow from the expression; the proved canonical cocycle theorem
supplies the conjugating element. This discharges the normalization input of
the field-fixed-group assembly for 16.1.4(4), including `m = 1`. -/
theorem normalize_inner_coefficient
    (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (a : MulAut (BinaryCarrier n hn))
    (ha : a^2 = 1) (houter : a ∉ MulAut.innerSubgroup (BinaryCarrier n hn))
    (g : BinaryCarrier n hn) (e : CoefficientAut (binaryParameters n hn))
    (hform : a = MulAut.conj g * coefficientAction (binaryParameters n hn) e) :
    ∃ b : MulAut (BinaryCarrier n hn), ∀ x, b (a x) =
      coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) (b x) :=
  normalize_of_cocycle_solutions n hn m hm hnm
    (canonical_cocycle_solutions n hn m hm hnm) a ha houter g e hform

end Triality.Standard.EvenField.NormalForm
