module
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Characters factoring through the symmetric-three quotient

A normal subgroup of `S₃` containing one transposition contains every
transposition by conjugacy, hence is all of `S₃`. Therefore any character
factoring through a surjection onto `S₃` is trivial when it kills one lift of
a transposition. The target is arbitrary; the application uses the sign
character on the binary wreath kernel.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the
normal-base calculation in Section 6, printed pp.399--400.
-/

public section
open Subgroup Equiv

namespace Equiv.Perm

/-- A normal subgroup of S₃ containing a transposition is all of S₃. -/
theorem normal_eq_top_of_isSwap_mem (N : Subgroup (Perm (Fin 3))) [N.Normal]
    {t : Perm (Fin 3)} (ht : t.IsSwap) (hN : t ∈ N) : N = ⊤ := by
  apply top_unique
  rw [← closure_isSwap, closure_le]
  rintro s ⟨c, d, hcd, rfl⟩
  obtain ⟨a, b, hab, rfl⟩ := ht
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_swap hab hcd)
  rw [← hg]
  exact (inferInstance : N.Normal).conj_mem _ hN g

end Equiv.Perm

namespace MonoidHom

/-- A homomorphism factoring through S₃ vanishes if it kills a lift of a
transposition. The target may be any group. -/
theorem eq_one_of_ker_le_of_swap {H K : Type*} [Group H] [Group K]
    (π : H →* Perm (Fin 3)) (hπ : Function.Surjective π) (χ : H →* K)
    (hker : π.ker ≤ χ.ker) (t : H) (ht : (π t).IsSwap) (hχt : χ t = 1) :
    χ = 1 := by
  let : (χ.ker.map π).Normal := (inferInstance : χ.ker.Normal).map π hπ
  have htop : χ.ker.map π = ⊤ := Perm.normal_eq_top_of_isSwap_mem _ ht
    (mem_map.mpr ⟨t, hχt, rfl⟩)
  apply ker_eq_top_iff.mp
  have hh := congrArg (Subgroup.comap π) htop
  simpa only [comap_map_eq, sup_of_le_left hker, comap_top] using hh

end MonoidHom
