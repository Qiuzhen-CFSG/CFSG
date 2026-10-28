module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow

/-!
# Placing an arbitrary Rudvalis Sylow subgroup in a max4 conjugate

The checked ATLAS max4 subgroup contains an ambient Sylow two-subgroup.
Sylow conjugacy places any prescribed Sylow subgroup in an actual conjugate
of max4 and supplies its group equivalence. This is the choice of M* over
the prescribed S* in Aschbacher--Smith I.2.2(7), printed p.412.

The choice alone does not identify the core or its two module factors.
Those calculations must concern these actual subgroups.
-/

namespace Rudvalis.CoveringIncidence

open Subgroup SylowOvergroups

/-- A literal conjugate of the fixed fourth ATLAS subgroup. -/
@[expose] public def conjugateMax4 (g : Model) : Subgroup Model :=
  max4.map (MulAut.conj g).toMonoidHom

/-- Conjugation provides the actual model equivalence. -/
public def conjugateMax4Equiv (g : Model) : max4 ≃* conjugateMax4 g :=
  (MulAut.conj g).subgroupMap max4

/-- The prescribed ambient Sylow lies in a conjugate of the fixed max4 group. -/
public theorem exists_conjugateMax4_over_sylow (S : Sylow 2 Model) :
    ∃ g : Model, (S : Subgroup Model) ≤ conjugateMax4 g := by
  obtain ⟨T, hT⟩ := max4ContainsSylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model T S
  refine ⟨g, ?_⟩
  rw [← hg]
  exact map_mono hT

end Rudvalis.CoveringIncidence
