module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.Descent
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.ExteriorDescent
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.CommutatorImage
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.QuadraticTransport
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.ScalarQuotients
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The minus-six/unitary-four comparison

For every field `F` of order `2^n`, with `n > 1`, the independently constructed
minus-six projective orthogonal group is isomorphic to PSU₄ over the quadratic
extension of a field of order `2^n`. The sole additional input is simplicity
of the original projective orthogonal carrier, inherited by the Theorem D
consumer from its ambient simple group.

Quadratic coordinate transport carries this simplicity to the norm-model
commutator. The proved unitary exterior descent and exact commutator-image
theorem then give `specialEquivMinusOmega`, whose action is intertwined with
the actual six-minor representation. The scalar and projective maps have
trivial kernel in characteristic two, giving `projectiveEquiv` and the final
field-and-form witness `exists_comparison`. Its Hermitian conjugation is the
`2^n`-power map on a matrix field of order `(2^n)^2`.

The original conditional assembly interfaces are retained; all three of their
mathematical inputs are supplied in the final construction below.
Sources: GLS3 §2.7; Aschbacher–Smith A.2.18, printed p.40, and Theorem D,
printed pp.1078–1079.
-/

public noncomputable section
namespace ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary

section Conditional

variable (n : ℕ) [NeZero n]

/-- An exact image theorem upgrades the faithful action to an actual equivalence. -/
def specialEquivOmega_of_range (hD : Descends n)
    (himage : (orthogonalAction n hD).range = commutator (FullOrthogonal n)) :
    SU n ≃* Omega n :=
  (MonoidHom.ofInjective (orthogonalAction_injective n hD)).trans
    (MulEquiv.subgroupCongr himage)

/-- This equivalence is induced by the constructed quadratic exterior action. -/
@[simp] theorem specialEquivOmega_of_range_apply (hD : Descends n)
    (himage : (orthogonalAction n hD).range = commutator (FullOrthogonal n)) (g : SU n) :
    (specialEquivOmega_of_range n hD himage g).val = orthogonalAction n hD g := by rfl

/-- The existing characteristic-two SU₄ projection, with its literal map retained. -/
def specialEquivProjective :
    SU n ≃* ProjectiveSpecialUnitaryMatrixGroup (unitaryForm n) :=
  MulEquiv.ofBijective (UnitaryFourFlag.project (Field n) (unitaryForm n))
    ⟨UnitaryFourFlag.project_injective (Field n) (unitaryForm n),
      UnitaryFourFlag.project_surjective (Field n) (unitaryForm n)⟩

@[simp] theorem specialEquivProjective_apply (g : SU n) :
    specialEquivProjective n g = UnitaryFourFlag.project (Field n) (unitaryForm n) g := by rfl

variable {F : Type} [_root_.Field F] [Finite F]

/-- A full quadratic-group comparison preserves the literal commutator subgroup. -/
def omegaEquiv_of_fullEquiv
    (e : Minus.Orthogonal F (Minus.Space F 2) (Minus.quadraticForm F 3) ≃*
      FullOrthogonal n) :
    Minus.Omega F (Minus.Space F 2) (Minus.quadraticForm F 3) ≃* Omega n :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective, ← commutator_def]))

@[simp] theorem omegaEquiv_of_fullEquiv_apply
    (e : Minus.Orthogonal F (Minus.Space F 2) (Minus.quadraticForm F 3) ≃*
      FullOrthogonal n)
    (g : Minus.Omega F (Minus.Space F 2) (Minus.quadraticForm F 3)) :
    (omegaEquiv_of_fullEquiv n e g).val = e g.val := by rfl

variable [CharP F 2]

/-- The optional simplicity premise for the image calculation comes from the
original projective carrier, without an independent model-simplicity theorem. -/
theorem omega_isSimple_of_fullEquiv [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)]
    (e : Minus.Orthogonal F (Minus.Space F 2) (Minus.quadraticForm F 3) ≃*
      FullOrthogonal n) : IsSimpleGroup (Omega n) :=
  ((omegaEquiv_of_fullEquiv n e).symm.trans (minusOmegaEquivProjective 3)).isSimpleGroup

/-- Composition of the genuine two projective maps and the full-group comparison.
The descent and image premises still have to be supplied by their producers. -/
def projectiveEquiv_of_descent_range_transport (hD : Descends n)
    (himage : (orthogonalAction n hD).range = commutator (FullOrthogonal n))
    (e : Minus.Orthogonal F (Minus.Space F 2) (Minus.quadraticForm F 3) ≃*
      FullOrthogonal n) :
    ClassicalGroup.POmegaMinus 3 F ≃* ProjectiveSpecialUnitaryMatrixGroup (unitaryForm n) :=
  (minusOmegaEquivProjective 3).symm.trans ((omegaEquiv_of_fullEquiv n e).trans
    ((specialEquivOmega_of_range n hD himage).symm.trans
      (specialEquivProjective n)))

/-- The comparison respects the actual scalar-quotient representative. -/
@[simp] theorem projectiveEquiv_of_descent_range_transport_apply (hD : Descends n)
    (himage : (orthogonalAction n hD).range = commutator (FullOrthogonal n))
    (e : Minus.Orthogonal F (Minus.Space F 2) (Minus.quadraticForm F 3) ≃*
      FullOrthogonal n)
    (g : Minus.Omega F (Minus.Space F 2) (Minus.quadraticForm F 3)) :
    projectiveEquiv_of_descent_range_transport n hD himage e
      (minusOmegaEquivProjective 3 g) =
        UnitaryFourFlag.project (Field n) (unitaryForm n)
          ((specialEquivOmega_of_range n hD himage).symm (omegaEquiv_of_fullEquiv n e g)) := by
  simp only [projectiveEquiv_of_descent_range_transport, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, specialEquivProjective_apply]

omit [CharP F 2] in
/-- The final coefficient-field and Hermitian-form witnesses, conditional on
the three independent mathematical inputs named in the theorem. -/
theorem exists_comparison_of_descent_range_transport (hcard : Nat.card F = 2 ^ n)
    (hD : Descends n)
    (himage : (orthogonalAction n hD).range = commutator (FullOrthogonal n))
    (e : Minus.Orthogonal F (Minus.Space F 2) (Minus.quadraticForm F 3) ≃*
      FullOrthogonal n) :
    ∃ (E : Type) (_ : _root_.Field E) (_ : Finite E) (J : HermitianForm 4 E),
      Nat.card E = (2 ^ n) ^ 2 ∧ (∀ x, J.conj x = x ^ (2 ^ n)) ∧
        Nonempty (ClassicalGroup.POmegaMinus 3 F ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := by
    apply ringChar.of_eq
    apply FiniteField.even_card_iff_char_two.mpr
    rw [← Nat.card_eq_fintype_card, hcard]
    exact Nat.mod_eq_zero_of_dvd
      (even_iff_two_dvd.mp (even_two.pow_of_ne_zero (NeZero.ne n)))
  exact ⟨Field n, inferInstance, inferInstance, unitaryForm n,
    card_field n, unitaryForm_conj n,
    ⟨projectiveEquiv_of_descent_range_transport n hD himage e⟩⟩

end Conditional

variable (n : ℕ) [NeZero n]
variable {F : Type} [_root_.Field F] [Finite F]

omit [NeZero n] in
private theorem charP_two_of_card (hcard : Nat.card F = 2 ^ n) : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by
    simpa only [← Nat.card_eq_fintype_card] using hcard)

/-- The exterior square identifies SU₄ with the literal commutator of the chosen
minus-six form. Its only model premise is inherited simplicity of the original
projective carrier; descent, image equality and coordinate transport are proved. -/
def specialEquivMinusOmega (hn : 1 < n) (hcard : Nat.card F = 2 ^ n)
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)] :
    SU n ≃* Minus.Omega F (Minus.Space F 2) (Minus.quadraticForm F 3) := by
  let : CharP F 2 := charP_two_of_card n hcard
  let : IsSimpleGroup (Omega n) := omega_isSimple_of_fullEquiv n (fullOrthogonalEquiv n hcard)
  exact (specialEquivOmega_of_range n (descends n)
    (orthogonalAction_range_eq_commutator n (descends n) hn)).trans
      (omegaEquiv_of_fullEquiv n (fullOrthogonalEquiv n hcard)).symm

/-- The assembled equivalence acts on the original minus space by the actual
exterior square after the semilinear quadratic-coordinate change. -/
theorem specialEquivMinusOmega_intertwines (hn : 1 < n) (hcard : Nat.card F = 2 ^ n)
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)] (g : SU n) (v : Minus.Space F 2) :
    toBivector n (quadraticCoordinates n hcard ((specialEquivMinusOmega n hn hcard g).val.val v)) =
      exterior n g (toBivector n (quadraticCoordinates n hcard v)) := by
  have he : fullOrthogonalEquiv n hcard (specialEquivMinusOmega n hn hcard g).val =
      orthogonalAction n (descends n) g := by
    change ((omegaEquiv_of_fullEquiv n (fullOrthogonalEquiv n hcard))
      (specialEquivMinusOmega n hn hcard g)).val = _
    simp only [specialEquivMinusOmega, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
      specialEquivOmega_of_range_apply]
  rw [← fullOrthogonalEquiv_apply, he, orthogonalAction_intertwines]

/-- The actual minus-six/PSU₄ comparison over every field of order `2^n`, using
only simplicity inherited from the original projective orthogonal carrier. -/
def projectiveEquiv (hn : 1 < n) (hcard : Nat.card F = 2 ^ n)
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)] :
    ClassicalGroup.POmegaMinus 3 F ≃* ProjectiveSpecialUnitaryMatrixGroup (unitaryForm n) := by
  let : CharP F 2 := charP_two_of_card n hcard
  exact ((specialEquivMinusOmega n hn hcard).trans (minusOmegaEquivProjective 3)).symm.trans
    (specialEquivProjective n)

/-- The final comparison sends the literal orthogonal scalar-quotient
representative to the literal projective unitary image of its exterior lift. -/
@[simp] theorem projectiveEquiv_apply (hn : 1 < n) (hcard : Nat.card F = 2 ^ n)
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)] (g : SU n) :
    projectiveEquiv n hn hcard
      (QuotientGroup.mk' (Minus.scalarSubgroup F (Minus.Space F 2) (Minus.quadraticForm F 3))
        (specialEquivMinusOmega n hn hcard g)) =
      UnitaryFourFlag.project (Field n) (unitaryForm n) g := by
  let : CharP F 2 := charP_two_of_card n hcard
  change specialEquivProjective n
    (((specialEquivMinusOmega n hn hcard).trans (minusOmegaEquivProjective 3)).symm
      (((specialEquivMinusOmega n hn hcard).trans (minusOmegaEquivProjective 3)) g)) = _
  rw [MulEquiv.symm_apply_apply, specialEquivProjective_apply]

omit [NeZero n] in
/-- The field-and-form witness consumed by the Theorem D model adapter.
The parameter `2^n` is the fixed-field order. No descent, commutator-image,
quadratic-transport or characteristic premise remains to be supplied. -/
theorem exists_comparison (hn : 1 < n) (hcard : Nat.card F = 2 ^ n)
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)] :
    ∃ (E : Type) (_ : _root_.Field E) (_ : Finite E) (J : HermitianForm 4 E),
      Nat.card E = (2 ^ n) ^ 2 ∧ (∀ x, J.conj x = x ^ (2 ^ n)) ∧
        Nonempty (ClassicalGroup.POmegaMinus 3 F ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : NeZero n := ⟨by omega⟩
  exact ⟨Field n, inferInstance, inferInstance, unitaryForm n,
    card_field n, unitaryForm_conj n, ⟨projectiveEquiv n hn hcard⟩⟩

end ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
