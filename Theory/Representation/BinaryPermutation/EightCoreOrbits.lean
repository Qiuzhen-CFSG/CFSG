module

public import Theory.Representation.BinaryPermutation.OrbitSizeSeparation
public import Theory.Representation.BinaryPermutation.CoreFixedLine

/-!
# Orbits of the eight-letter binary augmentation core

The five even weights give alternating-group orbits of sizes 1, 28, 70,
28 and 1. Equal orbit sizes therefore identify the weight up to complement.
Only the 256 binary words are used in the small kernel-checked counts;
no enumeration of alternating-group elements is required.

Source: Aschbacher--Smith, 12.2.16, printed pp.799--800.
-/

@[expose] public noncomputable section
namespace BinaryPermutation.EightCore
local instance : DecidablePred (· ∈ core (Fin 8)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype (core (Fin 8)) := Subtype.fintype _

def oneWord : core (Fin 8) := ⟨allOne (Fin 8), by rw [mem_core]; decide⟩

theorem weights (v : core (Fin 8)) :
    wordWeight v.val = 0 ∨ wordWeight v.val = 2 ∨ wordWeight v.val = 4 ∨
      wordWeight v.val = 6 ∨ wordWeight v.val = 8 := by
  revert v
  decide +kernel

private theorem counts :
    (Finset.univ.filter fun v : core (Fin 8) => wordWeight v.val = 0).card = 1 ∧
    (Finset.univ.filter fun v : core (Fin 8) => wordWeight v.val = 2).card = 28 ∧
    (Finset.univ.filter fun v : core (Fin 8) => wordWeight v.val = 4).card = 70 ∧
    (Finset.univ.filter fun v : core (Fin 8) => wordWeight v.val = 6).card = 28 ∧
    (Finset.univ.filter fun v : core (Fin 8) => wordWeight v.val = 8).card = 1 := by
  decide +kernel

def orbitSize (n : ℕ) : ℕ :=
  if n = 0 ∨ n = 8 then 1 else if n = 2 ∨ n = 6 then 28 else if n = 4 then 70 else 0

theorem weight_fiber_card (n : ℕ) :
    {v : core (Fin 8) | wordWeight v.val = n}.ncard = orbitSize n := by
  rw [show {v : core (Fin 8) | wordWeight v.val = n} =
    ↑(Finset.univ.filter fun v : core (Fin 8) => wordWeight v.val = n) by ext; simp,
    Set.ncard_coe_finset]
  by_cases h0 : n = 0
  · subst n; exact counts.1
  by_cases h2 : n = 2
  · subst n; exact counts.2.1
  by_cases h4 : n = 4
  · subst n; exact counts.2.2.1
  by_cases h6 : n = 6
  · subst n; exact counts.2.2.2.1
  by_cases h8 : n = 8
  · subst n; exact counts.2.2.2.2
  have he : (Finset.univ.filter fun v : core (Fin 8) => wordWeight v.val = n) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hn := (Finset.mem_filter.mp hv).2
    rcases weights v with h | h | h | h | h <;> omega
  simp [he,orbitSize,h0,h2,h4,h6,h8]

theorem orbit_card (v : core (Fin 8)) :
    (Set.range fun a : alternatingGroup (Fin 8) =>
      alternatingCoreRepresentation (Fin 8) a v).ncard = orbitSize (wordWeight v.val) := by
  rw [even_core_orbit_eq_weight (by decide),weight_fiber_card]

theorem weight_zero_iff (v : core (Fin 8)) : wordWeight v.val = 0 ↔ v = 0 := by
  change (Finset.univ.filter fun i => v.val i ≠ 0).card = 0 ↔ _
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
    forall_true_left, not_not]
  exact ⟨fun h => Subtype.ext (funext h), fun h => by simp [h]⟩

theorem weight_eight_iff (v : core (Fin 8)) : wordWeight v.val = 8 ↔ v = oneWord := by
  change (Finset.univ.filter fun i => v.val i ≠ 0).card =
    (Finset.univ : Finset (Fin 8)).card ↔ _
  rw [Finset.card_filter_eq_iff]
  simp only [Finset.mem_univ,forall_true_left]
  constructor
  · intro h
    apply Subtype.ext
    funext i
    exact ((by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (v.val i)).resolve_left (h i)
  · rintro rfl i
    exact one_ne_zero

theorem weight_complement (v : core (Fin 8)) :
    wordWeight (v + oneWord).val = 8 - wordWeight v.val := by
  have hh : ∀ x : Full (Fin 8), wordWeight (x + allOne (Fin 8)) = 8 - wordWeight x := by
    decide +kernel
  exact hh v.val

@[simp] theorem oneWord_add_oneWord : oneWord + oneWord = 0 := by decide

@[simp] theorem oneWord_ne_zero : oneWord ≠ 0 := by decide

theorem equal_size_iff (v w : core (Fin 8)) :
    orbitSize (wordWeight v.val) = orbitSize (wordWeight w.val) ↔
      wordWeight v.val = wordWeight w.val ∨
      wordWeight v.val + wordWeight w.val = 8 := by
  rcases weights v with hv | hv | hv | hv | hv <;>
    rcases weights w with hw | hw | hw | hw | hw <;>
    rw [hv,hw] <;> decide

end BinaryPermutation.EightCore
