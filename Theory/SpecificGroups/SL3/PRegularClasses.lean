module

public import Theory.SpecificGroups.SL3.PRegularClasses.GLIntertwiner
public import Theory.SpecificGroups.SL3.PRegularClasses.ScalarCorrection
public import Theory.SpecificGroups.SL3.PRegularClasses.CentralizerDeterminant
public import Mathlib.Algebra.Group.ConjFinite

/-!
# Counting odd-order conjugacy classes of SL₃

The two traces `trace(g)` and `trace(g⁻¹)` determine the characteristic
polynomial. Equal characteristic polynomials of odd-order elements give an
invertible intertwiner over the original field. Multiplying it by a commuting
matrix with the reciprocal determinant gives a conjugator in SL₃ itself.
Choosing representatives of the actual `ConjClasses.mk` image then embeds
the odd-order classes into `F × F`.

The prescribed-determinant theorem for semisimple centralizers supplies the
correction over every finite field: scale an invariant line along its invariant
complement, or use norm surjectivity from the irreducible cubic extension.
Thus `card_pRegularConjClasses_le` proves the bound `|F|²` for every finite
field of characteristic two, including the field of two elements. No
conjugacy-completeness or representation-classification hypothesis is used.
Source context: GLS III, 2.8.2 and 2.8.6(a),
`refs/KGroup/GLS3/chapter2.tex`, specialized to the literal SL₃ matrix group.
-/

namespace Theory.SpecificGroups.SL3.PRegularClasses

variable {F : Type*} [Field F]

/-- Correct a general-linear intertwiner using a matrix in the source
centralizer with precisely the reciprocal determinant. -/
public theorem isConj_of_intertwiner_of_commuting_det
    (g h : Matrix.SpecialLinearGroup (Fin 3) F)
    (D C : Matrix (Fin 3) (Fin 3) F) (hD : IsUnit D)
    (hDg : D * g.val = h.val * D) (hCg : C * g.val = g.val * C)
    (hC : C.det = D.det⁻¹) : IsConj g h := by
  have hd : D.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det D).mp hD).ne_zero
  let u : Matrix.SpecialLinearGroup (Fin 3) F :=
    ⟨D * C, by rw [Matrix.det_mul, hC]; exact mul_inv_cancel₀ hd⟩
  have hu : u * g = h * u := by
    apply Subtype.ext
    change (D * C) * g.val = h.val * (D * C)
    rw [Matrix.mul_assoc, hCg, ← Matrix.mul_assoc, hDg, Matrix.mul_assoc]
  exact isConj_iff.mpr ⟨u, mul_inv_eq_iff_eq_mul.mpr hu⟩

/-- Semisimple centralizer determinant surjectivity upgrades the proved GL₃
intertwiner to conjugacy in SL₃. -/
public theorem isConj_of_charpoly_eq_of_centralizer_determinants [CharP F 2]
    (hdet : ∀ A : Matrix (Fin 3) (Fin 3) F,
      Module.End.IsSemisimple (Matrix.toLin' A) →
      ∀ d : F, d ≠ 0 → ∃ C : Matrix (Fin 3) (Fin 3) F, C * A = A * C ∧ C.det = d)
    (g h : Matrix.SpecialLinearGroup (Fin 3) F)
    (hg : ¬ 2 ∣ orderOf g) (hh : ¬ 2 ∣ orderOf h)
    (hp : g.val.charpoly = h.val.charpoly) : IsConj g h := by
  obtain ⟨D, hD, hDg⟩ := exists_unit_intertwiner_of_charpoly_eq g h hg hh hp
  have hd : D.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det D).mp hD).ne_zero
  obtain ⟨C, hCg, hC⟩ := hdet g.val (isSemisimple_of_pRegular g hg) D.det⁻¹ (inv_ne_zero hd)
  exact isConj_of_intertwiner_of_commuting_det g h D C hD hDg hCg hC

/-- Odd-order elements with the same characteristic polynomial are conjugate
inside the literal SL₃ group over any finite field of characteristic two. -/
public theorem isConj_of_charpoly_eq [Finite F] [CharP F 2]
    (g h : Matrix.SpecialLinearGroup (Fin 3) F)
    (hg : ¬ 2 ∣ orderOf g) (hh : ¬ 2 ∣ orderOf h)
    (hp : g.val.charpoly = h.val.charpoly) : IsConj g h := by
  exact isConj_of_charpoly_eq_of_centralizer_determinants
    exists_commuting_det_of_isSemisimple g h hg hh hp

/-- The actual odd-order conjugacy classes inject into the two trace
parameters given the centralizer determinant input.
The bound includes the field of two elements. -/
public theorem card_pRegularConjClasses_le_of_centralizer_determinants
    [Finite F] [CharP F 2]
    (hdet : ∀ A : Matrix (Fin 3) (Fin 3) F,
      Module.End.IsSemisimple (Matrix.toLin' A) →
      ∀ d : F, d ≠ 0 → ∃ C : Matrix (Fin 3) (Fin 3) F, C * A = A * C ∧ C.det = d) :
    Nat.card (ConjClasses.mk ''
      {g : Matrix.SpecialLinearGroup (Fin 3) F | ¬ 2 ∣ orderOf g}) ≤ (Nat.card F) ^ 2 := by
  classical
  let P := ConjClasses.mk '' {g : Matrix.SpecialLinearGroup (Fin 3) F | ¬ 2 ∣ orderOf g}
  have hrep (c : P) : ∃ g : Matrix.SpecialLinearGroup (Fin 3) F,
      ¬ 2 ∣ orderOf g ∧ ConjClasses.mk g = c.val := c.property
  let r : P → Matrix.SpecialLinearGroup (Fin 3) F := fun c => (hrep c).choose
  have hrp (c : P) : ¬ 2 ∣ orderOf (r c) := (hrep c).choose_spec.1
  have hrc (c : P) : ConjClasses.mk (r c) = c.val := (hrep c).choose_spec.2
  let code : P → F × F := fun c => ((r c).val.trace, ((r c)⁻¹).val.trace)
  have hinj : Function.Injective code := by
    intro c d h
    apply Subtype.ext
    rw [← hrc c, ← hrc d]
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    apply isConj_of_charpoly_eq_of_centralizer_determinants hdet (r c) (r d) (hrp c) (hrp d)
    exact charpoly_eq_of_trace_eq (r c) (r d) (congrArg Prod.fst h) (congrArg Prod.snd h)
  simpa only [Nat.card_prod, pow_two] using Nat.card_le_card_of_injective code hinj

/-- There are at most `|F|²` odd-order conjugacy classes in the literal SL₃
group over a finite field of characteristic two, including the field of two
elements. No class-bound or representation-classification premise is needed. -/
public theorem card_pRegularConjClasses_le [Finite F] [CharP F 2] :
    Nat.card (ConjClasses.mk ''
      {g : Matrix.SpecialLinearGroup (Fin 3) F | ¬ 2 ∣ orderOf g}) ≤ (Nat.card F) ^ 2 := by
  exact card_pRegularConjClasses_le_of_centralizer_determinants
    exists_commuting_det_of_isSemisimple

/-- The class bound when scalar matrices suffice to correct determinants. -/
public theorem card_pRegularConjClasses_le_of_coprime [Finite F] [CharP F 2]
    (hc : (Nat.card F - 1).Coprime 3) :
    Nat.card (ConjClasses.mk ''
      {g : Matrix.SpecialLinearGroup (Fin 3) F | ¬ 2 ∣ orderOf g}) ≤ (Nat.card F) ^ 2 := by
  apply card_pRegularConjClasses_le_of_centralizer_determinants
  intro A _ d hd
  exact exists_commuting_det_of_coprime hc A d hd

/-- In particular the literal SL₃ over a field of two elements has at most
four odd-order conjugacy classes. -/
public theorem card_pRegularConjClasses_le_of_card_eq_two [Finite F] [CharP F 2]
    (hq : Nat.card F = 2) :
    Nat.card (ConjClasses.mk ''
      {g : Matrix.SpecialLinearGroup (Fin 3) F | ¬ 2 ∣ orderOf g}) ≤ (Nat.card F) ^ 2 := by
  apply card_pRegularConjClasses_le_of_coprime
  simp [hq]

end Theory.SpecificGroups.SL3.PRegularClasses
