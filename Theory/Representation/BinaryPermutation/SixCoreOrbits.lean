module

public import Theory.Representation.BinaryPermutation.OrbitSizeSeparation
public import Theory.Representation.BinaryPermutation.CoreFixedLine

/-!
# The two nonconstant orbits in the six-letter augmentation core

The constant word is the unique nonzero fixed vector. The remaining words
have weights two and four, with fifteen words in each class. Equal-weight
transport by actual even permutations identifies these classes with the
two orbits. Addition of the constant word interchanges them.

Source: Aschbacher–Smith, 12.2.16, printed p.800.
-/

@[expose] public noncomputable section
namespace BinaryPermutation

local instance : DecidablePred (· ∈ core (Fin 6)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype (core (Fin 6)) := Subtype.fintype _

/-- The literal all-one word, lying in the even-weight core. -/
def sixCoreConstant : core (Fin 6) := ⟨allOne (Fin 6), by decide⟩

theorem sixCoreConstant_ne_zero : sixCoreConstant ≠ 0 := by decide

theorem sixCoreConstant_fixed (a : alternatingGroup (Fin 6)) :
    alternatingCoreRepresentation (Fin 6) a sixCoreConstant = sixCoreConstant := by
  apply Subtype.ext
  funext i
  rfl

theorem sixCore_fixed_iff (v : core (Fin 6)) :
    (∀ a, alternatingCoreRepresentation (Fin 6) a v = v) ↔
      v = 0 ∨ v = sixCoreConstant := by
  constructor
  · intro hv
    obtain ⟨c,hc⟩ := (mem_constants_iff v.val).mp
      ((core_fixed_iff_constant (by norm_num) v).mp hv)
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · exact Or.inl (Subtype.ext (funext hc))
    · exact Or.inr (Subtype.ext (funext hc))
  · rintro (rfl | rfl) a
    · exact map_zero _
    · exact sixCoreConstant_fixed a

private theorem six_weights (v : core (Fin 6)) (h0 : v ≠ 0)
    (hz : v ≠ sixCoreConstant) : wordWeight v.val = 2 ∨ wordWeight v.val = 4 := by
  revert v
  decide +kernel

private theorem six_counts :
    (Finset.univ.filter fun v : core (Fin 6) => wordWeight v.val = 2).card = 15 ∧
    (Finset.univ.filter fun v : core (Fin 6) => wordWeight v.val = 4).card = 15 := by
  decide +kernel

/-- Both actual nonconstant orbits have fifteen elements. -/
theorem sixCore_orbit_card (v : core (Fin 6)) (h0 : v ≠ 0)
    (hz : v ≠ sixCoreConstant) :
    (Set.range fun a => alternatingCoreRepresentation (Fin 6) a v).ncard = 15 := by
  rw [even_core_orbit_eq_weight (by decide)]
  have he : {w : core (Fin 6) | wordWeight w.val = wordWeight v.val} =
      ↑(Finset.univ.filter fun w : core (Fin 6) => wordWeight w.val = wordWeight v.val) := by
    ext w
    simp
  rw [he, Set.ncard_coe_finset]
  rcases six_weights v h0 hz with hv | hv
  · simpa only [hv] using six_counts.1
  · simpa only [hv] using six_counts.2

private theorem six_complement_weights (v : core (Fin 6)) :
    wordWeight (v + sixCoreConstant).val = 6 - wordWeight v.val := by
  revert v
  decide +kernel

/-- Every nonconstant word lies in the orbit of v or of its complement. -/
theorem sixCore_paired_orbits (v w : core (Fin 6))
    (hv0 : v ≠ 0) (hvz : v ≠ sixCoreConstant)
    (hw0 : w ≠ 0) (hwz : w ≠ sixCoreConstant) :
    (∃ a, alternatingCoreRepresentation (Fin 6) a v = w) ∨
      (∃ a, alternatingCoreRepresentation (Fin 6) a (v + sixCoreConstant) = w) := by
  have ht (x y : core (Fin 6)) (he : wordWeight x.val = wordWeight y.val) :
      ∃ a, alternatingCoreRepresentation (Fin 6) a x = y := by
    obtain ⟨a,ha⟩ := exists_even_permutation_of_weight (by decide) x.val y.val he
    exact ⟨a,Subtype.ext ha⟩
  by_cases he : wordWeight v.val = wordWeight w.val
  · exact Or.inl (ht v w he)
  · right
    apply ht
    rw [six_complement_weights]
    rcases six_weights v hv0 hvz with hv | hv <;>
      rcases six_weights w hw0 hwz with hw | hw <;> omega

/-- Any two distinct nonconstant orbits cover all nonconstant words. -/
theorem sixCore_two_orbits (v w : core (Fin 6))
    (hv0 : v ≠ 0) (hvz : v ≠ sixCoreConstant)
    (hw0 : w ≠ 0) (hwz : w ≠ sixCoreConstant)
    (hne : ¬ ∃ a, alternatingCoreRepresentation (Fin 6) a v = w)
    (u : core (Fin 6)) (hu0 : u ≠ 0) (huz : u ≠ sixCoreConstant) :
    (∃ a, alternatingCoreRepresentation (Fin 6) a v = u) ∨
      (∃ a, alternatingCoreRepresentation (Fin 6) a w = u) := by
  obtain ⟨b,hb⟩ := (sixCore_paired_orbits v w hv0 hvz hw0 hwz).resolve_left hne
  rcases sixCore_paired_orbits v u hv0 hvz hu0 huz with he | ⟨a,ha⟩
  · exact Or.inl he
  · refine Or.inr ⟨a * b⁻¹, ?_⟩
    rw [← hb, ← Module.End.mul_apply, ← map_mul]
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using ha

end BinaryPermutation
