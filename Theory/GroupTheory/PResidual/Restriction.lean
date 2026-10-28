module
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.NormalSubgroup
/-!
# Restricting to a subgroup containing the residual

The p-residual of a finite group is p-perfect. Consequently any subgroup
containing it has the same embedded p-residual, by functoriality in both
directions. Source application: Aschbacher--Smith 2.5.12(2), pp.557--558.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem embedded_pResidual_eq_of_le_of_residual_le
    (p : ℕ) {X Y : Subgroup G} (hXY : X ≤ Y)
    (hRX : (pResidual p Y).map Y.subtype ≤ X) :
    (pResidual p X).map X.subtype = (pResidual p Y).map Y.subtype := by
  apply le_antisymm (embedded_pResidual_mono p hXY)
  let R := (pResidual p Y).map Y.subtype
  have hp : pResidual p R = ⊤ :=
    (pResidual_eq_top_iff p R).mpr (isPPerfect_embedded_pResidual p Y)
  have hh := map_pResidual_le p (inclusion hRX)
  rw [hp] at hh
  intro x hx
  have hx' : inclusion hRX (⟨x,hx⟩ : R) ∈ pResidual p X :=
    hh (mem_map_of_mem (inclusion hRX) (mem_top _))
  exact mem_map_of_mem X.subtype hx'
end Subgroup
