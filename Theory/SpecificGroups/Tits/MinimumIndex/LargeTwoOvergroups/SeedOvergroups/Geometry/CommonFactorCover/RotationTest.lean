module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.CosetData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.NormalForms

/-!
# Soundness of rotation matching certificates

The mixed-radix word code is decoded back to the exact conjugated normal form.
The boolean checker verifies membership in the original factor and row lists,
then tests the proposed product equality at the certified three-point base.
Its soundness theorem supplies exactly the rotation premise used by the
common-factor coverage assembly. No finite family is asserted checked here.
Source: Parrott (1972), §5, p.683 and the original geometry representatives.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover

/-- Encode the literal place, normal-form index, and rotation exponent. -/
def wordCode (j : Fin 38) (n : Fin 2048) (e : Nat) : Nat :=
  j.val + 38 * (n.val + 2048 * e)

theorem rowElement_encode (j : Fin 38) (n : Fin 2048) (e : Nat) :
    rowElement (wordCode j n e, 0) =
      conjugate j (atlas1600SylowTwoNormalForm n * rotation j ^ e) := by
  have hj : wordCode j n e % 38 = j.val := by unfold wordCode; omega
  have hn : wordCode j n e / 38 % 2048 = n.val := by unfold wordCode; omega
  have he : wordCode j n e / (38 * 2048) = e := by unfold wordCode; omega
  have hj' : (⟨wordCode j n e % 38, Nat.mod_lt _ (by decide)⟩ : Fin 38) = j := Fin.ext hj
  have hn' : (⟨wordCode j n e / 38 % 2048, Nat.mod_lt _ (by decide)⟩ : Fin 2048) = n := Fin.ext hn
  change conjugate ⟨wordCode j n e % 38, Nat.mod_lt _ (by decide)⟩
    (atlas1600SylowTwoNormalForm ⟨wordCode j n e / 38 % 2048, Nat.mod_lt _ (by decide)⟩ *
      rotation ⟨wordCode j n e % 38, Nat.mod_lt _ (by decide)⟩ ^
        (wordCode j n e / (38 * 2048))) = _
  rw [hj', hn', he]

/-- Check both list lookups and the three-point product identity. -/
def rotationTest (t : Fin 18) (j : Fin 38) (k : Fin 32) (e : Nat)
    (w : Fin 2048 × Row) : Bool :=
  decide (w.1 ∈ factorIndices t) && decide (w.2 ∈ rows t) &&
    sameBase (row (wordCode j (sylowRepresentatives t j k) e, 0))
      (fastNormalForm w.1 * row w.2)

/-- A successful check supplies a literal factor and original representative. -/
theorem rotationTest_sound (t : Fin 18) (j : Fin 38) (k : Fin 32) (e : Nat)
    (w : Fin 2048 × Row) (h : rotationTest t j k e w = true) :
    ∃ q ∈ factors t, ∃ r ∈ rows t,
      conjugate j (atlas1600SylowTwoNormalForm (sylowRepresentatives t j k) *
        rotation j ^ e) = q * rowElement r := by
  simp only [rotationTest, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨atlas1600SylowTwoNormalForm w.1, List.mem_map.mpr ⟨w.1, h.1.1, rfl⟩,
    w.2, h.1.2, ?_⟩
  rw [← rowElement_encode]
  apply (sameBase_iff _ _).mp
  change sameBase (rowElement (wordCode j (sylowRepresentatives t j k) e, 0)).val
    ((atlas1600SylowTwoNormalForm w.1).val * (rowElement w.2).val) = true
  simpa only [row_eq, fastNormalForm_eq] using h.2
end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover
