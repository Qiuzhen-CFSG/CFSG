module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Frobenius

/-!
# The eight-element subfield detected by seven-torsion

In a finite field of characteristic two, the fixed field of the third
Frobenius iterate has at most eight elements. A faithful multiplicative
copy of a group of order seven gives seven units in that subfield, so it
has exactly eight elements. This constructs the field within the given
ambient field, with its original operations.

Source: the finite-field step in Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.1.12, printed p.22.
-/

namespace FiniteField

/-- The subfield fixed by the third iterate of the binary Frobenius. -/
public def eightSubfield (E : Type*) [Field E] [CharP E 2] : Subfield E :=
  (iterateFrobenius E 2 3).eqLocusField (RingHom.id E)

private theorem eightSubfield_card_le (E : Type*) [Field E] [CharP E 2] [Finite E] :
    Nat.card (eightSubfield E) ≤ 8 := by
  classical
  let F := eightSubfield E
  let : Fintype F := Fintype.ofFinite F
  have hp : (Polynomial.X ^ 8 - Polynomial.X : Polynomial F) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero F (by decide)
  have hroot : (Finset.univ : Finset F).val ⊆ (Polynomial.X ^ 8 - Polynomial.X : Polynomial F).roots := by
    intro a _
    apply (Polynomial.mem_roots hp).mpr
    change (Polynomial.X ^ 8 - Polynomial.X : Polynomial F).eval a = 0
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
    apply Subtype.ext
    exact a.property
  have h := Polynomial.card_le_degree_of_subset_roots hroot
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq F (by decide)] at h
  simpa [Nat.card_eq_fintype_card] using h


/-- A faithful copy of a group of order seven supplies every nonzero element
of the eight-element subfield. The upper bound is the root bound for X⁸ − X. -/
public theorem eightSubfield_card_eq {E G : Type*} [Field E] [CharP E 2] [Finite E]
    [Group G] [Finite G] (hG : Nat.card G = 7)
    (f : G →* E) (hf : Function.Injective f) : Nat.card (eightSubfield E) = 8 := by
  let F := eightSubfield E
  let fF : G →* F :=
    { toFun g := ⟨f g, by
        change f g ^ 8 = f g
        have hp : g ^ 7 = 1 := by simpa [hG] using (pow_card_eq_one' (x := g))
        rw [show 8 = 7 + 1 from rfl, pow_succ, ← map_pow, hp, map_one, one_mul]⟩
      map_one' := Subtype.ext f.map_one
      map_mul' g h := Subtype.ext (f.map_mul g h) }
  let fu := fF.toHomUnits
  have hfu : Function.Injective fu := by
    intro g h he
    apply hf
    exact congrArg (fun u : Fˣ => (u.val : E)) he
  have hlo := Nat.card_le_card_of_injective fu hfu
  rw [hG, Nat.card_units] at hlo
  have hhi := eightSubfield_card_le E
  change 7 ≤ Nat.card (eightSubfield E) - 1 at hlo
  omega


end FiniteField
