module

public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.TraceParameters
public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.UnitaryIntertwiner
public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant
public import Mathlib.Algebra.Group.ConjFinite

/-!
# Odd-order class counting for special unitary three-space

The trace parameter takes values in the matrix field. Equal traces first give
an invertible linear intertwiner. A unitary correction, followed by a commuting
unitary matrix with the reciprocal determinant, makes this an SU₃ conjugator.
Choosing odd-order class representatives therefore gives the bound `|F|`.

The two correction results are proved over the quadratic binary finite field
and discharged in `isConj_of_trace_eq` and `card_pRegularConjClasses_le`.
The conditional interfaces are retained separately. The bound applies to the
full special unitary group and its cubic center, for every nondegenerate
Hermitian form and every exponent `s ≥ 2`.

Source context: GLS III, 2.8.2, 2.8.6(a), and 2.8.10(c),
`refs/KGroup/GLS3/chapter2.tex`. The catalogue application is
`CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.Catalogue.ClassBound`.
-/

namespace Theory.SpecificGroups.SU3.BinaryPRegularClasses
open Matrix BenderSuzuki.MatrixGroups
variable {F : Type*} [Field F]

/-- Multiply a unitary intertwiner by a commuting unitary matrix with reciprocal
determinant to obtain conjugacy in the full SU₃. -/
public theorem isConj_of_unitary_intertwiner_of_centralizer_determinants
    (J : HermitianForm 3 F) (g h : J.specialSubgroup)
    (hdet : ∀ d : Fˣ, J.conj (d : F) * (d : F) = 1 →
      ∃ C : J.unitarySubgroup, Commute C.val g.val ∧ GeneralLinearGroup.det C.val = d)
    (U : J.unitarySubgroup) (hU : U.val * g.val = h.val * U.val) : IsConj g h := by
  let d : Fˣ := (GeneralLinearGroup.det U.val)⁻¹
  have hd : J.conj (d : F) * (d : F) = 1 := by
    dsimp only [d]
    rw [Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply, map_inv₀, ← mul_inv,
      det_norm J U, inv_one]
  obtain ⟨C, hCg, hCd⟩ := hdet d hd
  let u : J.specialSubgroup := ⟨U.val * C.val,
    J.unitarySubgroup.mul_mem U.property C.property, by
      change GeneralLinearGroup.det (U.val * C.val) = 1
      rw [map_mul, hCd]
      exact mul_inv_cancel _⟩
  have hu : u * g = h * u := by
    apply Subtype.ext
    change (U.val * C.val) * g.val = h.val * (U.val * C.val)
    rw [mul_assoc, hCg.eq, ← mul_assoc, hU, mul_assoc]
  exact isConj_iff.mpr ⟨u, mul_inv_eq_iff_eq_mul.mpr hu⟩

section CharacteristicTwo
variable [CharP F 2]

/-- Equal traces give actual SU₃ conjugacy once the two independent unitary corrections are supplied. -/
public theorem isConj_of_trace_eq_of_unitary_corrections
    (J : HermitianForm 3 F)
    (hunitary : ∀ g h : J.specialSubgroup,
      ¬ 2 ∣ orderOf g → ¬ 2 ∣ orderOf h →
      ∀ D : GL (Fin 3) F, D * g.val = h.val * D →
        ∃ U : J.unitarySubgroup, U.val * g.val = h.val * U.val)
    (hdet : ∀ g : J.specialSubgroup, ¬ 2 ∣ orderOf g →
      ∀ d : Fˣ, J.conj (d : F) * (d : F) = 1 →
        ∃ C : J.unitarySubgroup, Commute C.val g.val ∧ GeneralLinearGroup.det C.val = d)
    (g h : J.specialSubgroup) (hg : ¬ 2 ∣ orderOf g) (hh : ¬ 2 ∣ orderOf h)
    (ht : g.val.val.trace = h.val.val.trace) : IsConj g h := by
  obtain ⟨D, hD⟩ := exists_GL_intertwiner_of_trace_eq J g h hg hh ht
  obtain ⟨U, hU⟩ := hunitary g h hg hh D hD
  exact isConj_of_unitary_intertwiner_of_centralizer_determinants J g h (hdet g hg) U hU

/-- The actual odd-order SU₃ classes inject into the matrix field, conditional
on unitary intertwiner correction and centralizer determinant surjectivity. -/
public theorem card_pRegularConjClasses_le_of_unitary_corrections [Finite F]
    (J : HermitianForm 3 F)
    (hunitary : ∀ g h : J.specialSubgroup,
      ¬ 2 ∣ orderOf g → ¬ 2 ∣ orderOf h →
      ∀ D : GL (Fin 3) F, D * g.val = h.val * D →
        ∃ U : J.unitarySubgroup, U.val * g.val = h.val * U.val)
    (hdet : ∀ g : J.specialSubgroup, ¬ 2 ∣ orderOf g →
      ∀ d : Fˣ, J.conj (d : F) * (d : F) = 1 →
        ∃ C : J.unitarySubgroup, Commute C.val g.val ∧ GeneralLinearGroup.det C.val = d) :
    Nat.card (ConjClasses.mk '' {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}) ≤ Nat.card F := by
  classical
  let P := ConjClasses.mk '' {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}
  have hrep (c : P) : ∃ g : J.specialSubgroup,
      ¬ 2 ∣ orderOf g ∧ ConjClasses.mk g = c.val := c.property
  let r : P → J.specialSubgroup := fun c => (hrep c).choose
  have hrp (c : P) : ¬ 2 ∣ orderOf (r c) := (hrep c).choose_spec.1
  have hrc (c : P) : ConjClasses.mk (r c) = c.val := (hrep c).choose_spec.2
  let code : P → F := fun c => (r c).val.val.trace
  have hinj : Function.Injective code := by
    intro c d he
    apply Subtype.ext
    rw [← hrc c, ← hrc d]
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    exact isConj_of_trace_eq_of_unitary_corrections J hunitary hdet
      (r c) (r d) (hrp c) (hrp d) he
  exact Nat.card_le_card_of_injective code hinj

end CharacteristicTwo

variable [Finite F] [Algebra (ZMod 2) F]

/-- Equal traces of odd-order binary SU₃ elements imply conjugacy in the full
special unitary group, for the original nondegenerate Hermitian form. -/
public theorem isConj_of_trace_eq
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (g h : J.specialSubgroup) (hg : ¬ 2 ∣ orderOf g) (hh : ¬ 2 ∣ orderOf h)
    (ht : g.val.val.trace = h.val.val.trace) : IsConj g h := by
  obtain ⟨U, hU⟩ := exists_unitary_intertwiner_of_trace_eq J s hs hcard hconj g h hg hh ht
  exact isConj_of_unitary_intertwiner_of_centralizer_determinants J g h
    (exists_unitary_centralizer_det J s hs hcard hconj g hg) U hU

/-- The full binary SU₃ group has at most `|F| = (2^s)^2` odd-order conjugacy
classes, including the case `s = 2` and the cubic center when `s` is odd. -/
public theorem card_pRegularConjClasses_le
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s)) :
    Nat.card (ConjClasses.mk '' {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}) ≤ Nat.card F := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  exact card_pRegularConjClasses_le_of_unitary_corrections J
    (exists_unitary_intertwiner_of_GL_intertwiner J s hs hcard hconj)
    (exists_unitary_centralizer_det J s hs hcard hconj)

end Theory.SpecificGroups.SU3.BinaryPRegularClasses
