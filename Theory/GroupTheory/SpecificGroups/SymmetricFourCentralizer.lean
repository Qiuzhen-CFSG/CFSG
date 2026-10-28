module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Involution centralizers in the symmetric group of degree four

The centralizer of a nonidentity involution in S₄ is a two-group. We verify
on the finite permutation model that every commuting permutation has eighth
power one, then use the elementwise criterion for a two-group. This is the
finite calculation used when lifting centralizers through a central two-kernel.
-/

namespace Equiv.Perm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem commuting_involution_pow_eight :
    ∀ t : Equiv.Perm (Fin 4), t ≠ 1 → t ^ 2 = 1 →
      ∀ s : Equiv.Perm (Fin 4), s * t = t * s → s ^ 8 = 1 := by decide

public theorem centralizer_involution_isTwoGroup (t : Equiv.Perm (Fin 4))
    (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    IsPGroup 2 (Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 4)))) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro s
  exact ⟨3, Subtype.ext (commuting_involution_pow_eight t ht ht2 s
    (Subgroup.mem_centralizer_singleton_iff.mp s.property))⟩

end Equiv.Perm
