module

public import Theory.GroupTheory.DoubleCoverCentralizer.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Automorphisms centralizing a perfect subgroup's inner action

For a perfect subgroup J of H, the centralizer of Inn(J) in Aut(H) is
exactly the pointwise fixer of J. Commuting with each inner automorphism
first says that two maps from J agree modulo Z(H). Uniqueness of lifts
from a perfect group across a central kernel removes this discrepancy.

This applies without a centerless hypothesis on H or J and retains the
actual embedded subgroup. It supplies the automorphism-centralizer bridge
in Aschbacher–Smith 16.3.5, printed pp.1178–1179 (1 March 2004 manuscript).
-/

public section
namespace Theory.GroupTheory.PerfectSubgroupAutomorphismFixer
open Subgroup Theory.GroupTheory

variable {H : Type*} [Group H]
/-- Commuting with the inner action is equivalent to fixing the perfect subgroup pointwise. -/
theorem inner_centralizer_eq_fixer (J : Subgroup H) [Group.IsPerfect J] :
    centralizer (J.map (MulAut.conj : H →* MulAut H) : Set (MulAut H)) =
      fixingSubgroup (MulAut H) (J : Set H) := by
  ext a
  rw [mem_fixingSubgroup_iff]
  constructor
  · intro ha
    have he : a.toMonoidHom.comp J.subtype = J.subtype := by
      apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
        (MulAut.conj : H →* MulAut H) (by rw [DoubleCoverCentralizer.conj_kernel])
      apply MonoidHom.ext
      intro j
      have hj := mem_centralizer_iff.mp ha (MulAut.conj (j : H))
        (mem_map_of_mem MulAut.conj j.property)
      change MulAut.conj (a (j : H)) = MulAut.conj (j : H)
      calc
        _ = a * MulAut.conj (j : H) * a⁻¹ := by ext x; simp [MulAut.conj_apply]
        _ = MulAut.conj (j : H) := by rw [← hj]; group
    intro j hj
    exact DFunLike.congr_fun he ⟨j, hj⟩
  · intro ha b hb
    obtain ⟨j, hj, rfl⟩ := hb
    ext x
    change j * a x * j⁻¹ = a (j * x * j⁻¹)
    simp only [map_mul, map_inv, show a j = j from ha j hj]

end Theory.GroupTheory.PerfectSubgroupAutomorphismFixer
