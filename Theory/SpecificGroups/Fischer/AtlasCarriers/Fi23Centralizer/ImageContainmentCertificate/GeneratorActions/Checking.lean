module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.Tables
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.ImageWords

/-!
# Bounded table certificates for the eight generator actions

A balanced Boolean check covers a block of 128 inputs. Twenty-eight blocks
suffice for both the 3510 Fi22 letters and the 3511 marked Fi23 coordinates.
Its soundness turns kernel reductions into pointwise equations. Multiplication
and inversion then identify tables with the literal Fi22 word nodes, without
expanding the words. Inversion is justified by the already known permutation,
so a separate bijectivity certificate for the proposed table is unnecessary.

These interfaces serve the explicit Fi23-to-Fi22 action comparisons used for
GLS3 Table 5.3u; no centralizer description is assumed here.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.GeneratorActions

/-- Balanced checking avoids a linear-depth reduction of a whole finite map. -/
def checkRange (f : Nat → Bool) : Nat → Nat → Bool
  | 0, start => f start
  | d + 1, start => checkRange f d start && checkRange f d (start + 2^d)

theorem checkRange_spec (f : Nat → Bool) (d start : Nat) :
    checkRange f d start = true ↔
      ∀ i, start ≤ i → i < start + 2^d → f i = true := by
  induction d generalizing start with
  | zero =>
    simp only [checkRange, pow_zero]
    constructor
    · intro h i hi hi'
      have : i = start := by omega
      simpa [this] using h
    · intro h
      exact h start le_rfl (by omega)
  | succ d ih =>
    rw [checkRange, Bool.and_eq_true, ih, ih, pow_succ]
    constructor
    · rintro ⟨hl, hr⟩ i hi hi'
      by_cases h : i < start + 2^d
      · exact hl i hi h
      · exact hr i (by omega) (by omega)
    · intro h
      constructor
      · intro i hi hi'
        exact h i hi (by omega)
      · intro i hi hi'
        exact h i (by omega) (by omega)

/-- Out-of-range padding is ignored, with no modular aliasing of inputs. -/
def mapCheck {n m : Nat} (f g : Fin n → Fin m) (i : Nat) : Bool :=
  if h : i < n then f ⟨i, h⟩ == g ⟨i, h⟩ else true

/-- The same block contract handles the Fi22 letters and the extra `none` point. -/
theorem map_eq_of_checks {n m : Nat} (hn : n ≤ 3584) (f g : Fin n → Fin m)
    (h : ∀ b : Fin 28, checkRange (mapCheck f g) 7 (128 * b.val) = true)
    (i : Fin n) : f i = g i := by
  have hb : i.val / 128 < 28 := by omega
  have hi := (checkRange_spec (mapCheck f g) 7 (128 * (i.val / 128))).mp
    (h ⟨i.val / 128, hb⟩) i.val (by omega) (by norm_num; omega)
  simpa only [mapCheck, dif_pos i.isLt, beq_iff_eq] using hi

/-- A table is identified with the actual permutation only by a proof of this relation. -/
def Represents (p : Equiv.Perm (Fin 3510)) (t : Nat) : Prop :=
  ∀ x, p x = tableAction t x

theorem Represents.mul {p q : Equiv.Perm (Fin 3510)}
    {a b c : Nat} (hp : Represents p a) (hq : Represents q b)
    (hc : ∀ x, tableAction a (tableAction b x) = tableAction c x) :
    Represents (p * q) c := by
  intro x
  rw [Equiv.Perm.mul_apply, hp, hq, hc]

theorem Represents.inv {p : Equiv.Perm (Fin 3510)}
    {a b : Nat} (hp : Represents p a)
    (hb : ∀ x, tableAction a (tableAction b x) = x) : Represents p⁻¹ b := by
  intro x
  apply p.injective
  rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply, hp, hb]

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.GeneratorActions
