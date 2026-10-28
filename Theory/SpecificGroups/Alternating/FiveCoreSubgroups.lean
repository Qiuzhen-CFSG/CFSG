module
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.PCoreImage

/-!
# Proper subgroups containing the two-core of an A5 extension

A proper subgroup containing the whole two-core has a proper image in the
alternating-five quotient. That image is solvable, and the two-core is a
solvable kernel, so the original subgroup is solvable. Containment of the
whole core is essential: a proper complement can have the full A5 image.

Source application: Aschbacher–Smith 10.2.10, printed p.753, for the
opposite block's point stabilizer on the original full module.
-/

public section
open Subgroup
namespace alternatingGroup
variable {K : Type*} [Group K] [Finite K]

/-- A proper subgroup over the full two-core of an A5 extension is solvable. -/
theorem isSolvable_proper_subgroup_containing_twoCore
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (H : Subgroup K) (hne : H ≠ ⊤) (hcore : pCore 2 K ≤ H) :
    Group.IsSolvable H := by
  let q := QuotientGroup.mk' (pCore 2 K)
  have hproper : H.map q ≠ ⊤ := by
    intro he
    apply hne
    have hh := congrArg (comap q) he
    rwa [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hcore,comap_top] at hh
  let : Group.IsSolvable (H.map q) := isSolvable_subgroup_of_equiv_five e _ hproper
  let : Group.IsNilpotent (pCore 2 K) := (pCore_isPGroup (p := 2) (G := K)).isNilpotent
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsSolvable ((H.map q).comap q) := isSolvable_comap_of_solvable_ker q _
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion (le_comap_map q H)) (inclusion_injective _)
end alternatingGroup
