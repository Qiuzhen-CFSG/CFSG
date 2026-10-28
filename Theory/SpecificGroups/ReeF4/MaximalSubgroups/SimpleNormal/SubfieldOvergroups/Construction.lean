module

public import Theory.SpecificGroups.ReeF4.Model
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Intrinsic subfield fixed groups inside the concrete Ree group

Inside `Model m`, the standard subgroup at parameter `k` is cut out by the
smaller exceptional power `σ^(2*k+1)`. Divisibility of odd degrees gives
containment of these actual fixed-point subgroups. In particular the subgroup
at parameter zero is defined by `σ`, with no passage to a derived subgroup.

These definitions are the objects used in the subfield case of Malle,
J. Algebra 139 (1991), 52–69, DOI 10.1016/0021-8693(91)90283-E.
Identification with the smaller coefficient-field model, strictness, and the
normalizer calculation are separate obligations.
-/

@[expose] public section

namespace ReeF4.Subfield

open Subgroup

noncomputable section

/-- The full smaller exceptional fixed group, considered inside `Model m`. -/
def fixedSubfield (m k : ℕ) : Subgroup (Model m) :=
  MonoidHom.eqLocus
    ((exceptionalEndomorphism m ^ (2 * k + 1)).comp (toSplitGroup m))
    (toSplitGroup m)

@[simp] theorem mem_fixedSubfield (m k : ℕ) (x : Model m) :
    x ∈ fixedSubfield m k ↔
      (exceptionalEndomorphism m ^ (2 * k + 1)) (toSplitGroup m x) =
        toSplitGroup m x := Iff.rfl

/-- A fixed point of an endomorphism is fixed by all its natural powers. -/
theorem pow_apply_eq_of_apply_eq {G : Type*} [Monoid G]
    (f : Monoid.End G) {x : G} (hx : f x = x) (n : ℕ) : (f ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ']
      change f ((f ^ n) x) = x
      rw [ih, hx]

/-- Fixed-point subgroups increase when their exceptional exponents divide. -/
theorem fixedSubfield_mono (m : ℕ) {k l : ℕ}
    (hdiv : (2 * k + 1) ∣ (2 * l + 1)) :
    fixedSubfield m k ≤ fixedSubfield m l := by
  obtain ⟨a, ha⟩ := hdiv
  intro x hx
  rw [mem_fixedSubfield] at hx ⊢
  rw [ha, pow_mul]
  exact pow_apply_eq_of_apply_eq _ hx a

/-- The ambient parameter recovers the whole Ree group. -/
@[simp] theorem fixedSubfield_self (m : ℕ) : fixedSubfield m m = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  rw [mem_fixedSubfield, ← reeTwist_eq_pow]
  exact reeTwist_toSplitGroup m x

/-- The derived subgroup of the full standard subfield group in the ambient
Ree group. It is deliberately distinct from `fixedSubfield`. -/
def derivedSubfield (m k : ℕ) : Subgroup (Model m) :=
  ⁅fixedSubfield m k, fixedSubfield m k⁆

theorem derivedSubfield_eq_map (m k : ℕ) :
    derivedSubfield m k =
      (_root_.commutator (fixedSubfield m k)).map (fixedSubfield m k).subtype :=
  (map_subtype_commutator _).symm

theorem derivedSubfield_le (m k : ℕ) : derivedSubfield m k ≤ fixedSubfield m k :=
  commutator_le_self _

/-- The easy inclusion in the eventual normalizer calculation follows from
normality of the derived subgroup in the full fixed group. -/
theorem fixedSubfield_le_normalizer_derived (m k : ℕ) :
    fixedSubfield m k ≤ normalizer (derivedSubfield m k : Set (Model m)) :=
  normalizer_commutator_ge_left _ _

end

end ReeF4.Subfield
