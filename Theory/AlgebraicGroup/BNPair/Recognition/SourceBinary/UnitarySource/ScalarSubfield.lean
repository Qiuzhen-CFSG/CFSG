module
public import Theory.FieldTheory.RootsOfUnityCard
public import Mathlib.Algebra.CharP.Frobenius

/-!
# Scalar subfields detected inside the actual commuting field

The fixed field of the nth binary Frobenius is constructed inside the given
field, with its inherited operations. If 2^n-1 divides the unit-group order,
roots of unity give its lower cardinal bound and X^(2^n)-X gives the upper
bound. Hence its order is exactly 2^n.

A faithful scalar actor of that full unit order maps bijectively onto the
nonzero scalars. This identifies its actual operators, not merely an
abstract finite field with the same order. CoreCoefficients applies the
construction to the commuting ring of the original source core action.

Source: Fong--Seitz II (8B)--(8C), printed pp.201,203. The proof follows
the polynomial-count method also used in Theory.FieldTheory.EightElementSubfield.
-/

public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.ScalarSubfield
variable (E : Type*) [Field E] [CharP E 2]

@[expose] def field (n : ℕ) : Subfield E :=
  (iterateFrobenius E 2 n).eqLocusField (RingHom.id E)

theorem mem_field (n : ℕ) (a : E) : a ∈ field E n ↔ a ^ (2 ^ n) = a := Iff.rfl

variable [Finite E]

theorem card_le (n : ℕ) (hn : 0 < n) : Nat.card (field E n) ≤ 2 ^ n := by
  classical
  let F := field E n
  let : Fintype F := Fintype.ofFinite F
  have hq : 1 < 2 ^ n := one_lt_pow₀ (by decide) hn.ne'
  have hp : (Polynomial.X ^ (2 ^ n) - Polynomial.X : Polynomial F) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero F hq
  have hr : (Finset.univ : Finset F).val ⊆
      (Polynomial.X ^ (2 ^ n) - Polynomial.X : Polynomial F).roots := by
    intro a _
    apply (Polynomial.mem_roots hp).mpr
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero]
    apply Subtype.ext
    exact a.property
  have hd := Polynomial.card_le_degree_of_subset_roots hr
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq F hq] at hd
  simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hd

private def rootsMap (n : ℕ) : rootsOfUnity (2 ^ n - 1) E →* field E n where
  toFun a := ⟨(a.val : E), by
    change (a.val : E) ^ (2 ^ n) = (a.val : E)
    have ha : (a.val : E) ^ (2 ^ n - 1) = 1 := by
      exact congrArg Units.val a.property
    calc
      _ = (a.val : E) ^ (2 ^ n - 1 + 1) :=
        congrArg (fun k => (a.val : E) ^ k)
          (Nat.sub_add_cancel (Nat.one_le_pow n 2 (by decide))).symm
      _ = _ := by rw [pow_succ, ha, one_mul]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem card_eq (n : ℕ) (hn : 0 < n)
    (hd : 2 ^ n - 1 ∣ Nat.card E - 1) : Nat.card (field E n) = 2 ^ n := by
  have hq : 1 < 2 ^ n := one_lt_pow₀ (by decide) hn.ne'
  let : NeZero (2 ^ n - 1) := ⟨by omega⟩
  have hi : Function.Injective (rootsMap E n).toHomUnits := by
    intro a b he
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun u : (field E n)ˣ => (u.val : E)) he
  have hlo := Nat.card_le_card_of_injective _ hi
  rw [FiniteField.card_rootsOfUnity_of_dvd E _ hd, Nat.card_units] at hlo
  have hhi := card_le E n hn
  omega

variable {A : Type*} [Group A]

@[expose] def actorMap (n : ℕ) (hA : Nat.card A = 2 ^ n - 1) (f : A →* E) :
    A →* field E n where
  toFun a := ⟨f a, by
    change f a ^ (2 ^ n) = f a
    have ha : a ^ (2 ^ n - 1) = 1 := hA ▸ pow_card_eq_one' (x := a)
    rw [← Nat.sub_add_cancel (show 1 ≤ 2 ^ n from Nat.one_le_pow n 2 (by decide)),
      pow_succ, ← map_pow, ha, map_one, one_mul]⟩
  map_one' := Subtype.ext f.map_one
  map_mul' a b := Subtype.ext (f.map_mul a b)

theorem actorMap_bijective (n : ℕ) (hn : 0 < n) (hA : Nat.card A = 2 ^ n - 1)
    (f : A →* E) (hf : Function.Injective f) :
    Function.Bijective (actorMap E n hA f).toHomUnits := by
  have hi : Function.Injective (actorMap E n hA f).toHomUnits := by
    intro a b he
    apply hf
    exact congrArg (fun u : (field E n)ˣ => (u.val : E)) he
  have hf' : Function.Injective f.toHomUnits := by
    intro a b he
    exact hf (congrArg Units.val he)
  have hd : 2 ^ n - 1 ∣ Nat.card E - 1 := by
    rw [← hA, ← Nat.card_units]
    exact Subgroup.card_dvd_of_injective _ hf'
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨hi, by rw [Nat.card_units, card_eq E n hn hd, hA]⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.ScalarSubfield
