module
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.Data.Set.Card

/-!
# Transitivity from a strict orbit-size bound

Two disjoint orbits cannot both contain more than half of a finite invariant
set. This counting observation is used for the actual975-point mixed Rudvalis
orbit, after the native stabilizer bound gives orbit size at least780.
-/

public section
noncomputable section
namespace MulAction
variable {K Ω:Type*} [Group K] [MulAction K Ω] [Finite Ω]

/-- If every orbit in a finite invariant set exceeds half its size, the set is transitive. -/
theorem transitive_of_large_orbits (S:Set Ω)
    (hS:∀k:K,∀x∈S,k•x∈S)
    (hl:∀x∈S,S.ncard<2*(orbit K x).ncard) (x y:Ω) (hx:x∈S) (hy:y∈S) :
    ∃k:K,k•x=y := by
  have hsub (z:Ω) (hz:z∈S):orbit K z⊆S:=by
    rintro w ⟨k,rfl⟩; exact hS k z hz
  rcases orbit.eq_or_disjoint (G := K) x y with he|hd
  · exact mem_orbit_iff.mp (he.symm ▸ mem_orbit_self y)
  · have hc:=Set.ncard_le_ncard (Set.union_subset (hsub x hx) (hsub y hy))
    rw [Set.ncard_union_eq hd] at hc
    have h1:=hl x hx
    have h2:=hl y hy
    omega
end MulAction
