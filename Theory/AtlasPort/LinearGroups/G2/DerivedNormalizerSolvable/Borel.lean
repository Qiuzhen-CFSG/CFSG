module

public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup
public import Theory.GroupTheory.SolvableNormalSup
public import Mathlib.GroupTheory.Nilpotent

/-!
# Solvability of the concrete G₂ Borel in characteristic two

The six positive root groups form a finite two-group. The split torus is
isomorphic to the product of two copies of the multiplicative field group,
so it is abelian. Torus normalization makes the positive-root subgroup normal
inside the Borel, and the root-by-torus decomposition proves solvability by
extension. Normality here is relative to the Borel.

This supplies the G₂ Borel used in Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined 1 March 2004 manuscript, proof of 15.3.49(k),
printed p.1144. The root product and torus parametrization are from the
licensed ATLAS port by Gerald Höhn and the ATLAS contributors; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.DerivedNormalizerSolvable
open Subgroup

variable {F : Type*} [Field F]

/-- The concrete split torus is solvable through its multiplicative parametrization. -/
theorem isSolvable_splitTorus : Group.IsSolvable (splitTorus (K := F)) := by
  exact Group.isSolvable_of_surjective (torusParameterEquiv (K := F)).surjective

/-- The finite positive-root group in characteristic two is solvable. -/
theorem isSolvable_unipotent [Finite F] [CharP F 2] :
    Group.IsSolvable (unipotent (K := F)) := by
  let : Group.IsNilpotent (unipotent (K := F)) :=
    LieParabolicSetup.unipotent_isTwoGroup.isNilpotent
  infer_instance

/-- The root-defined Borel is an extension of solvable groups. -/
theorem isSolvable_borel [Finite F] [CharP F 2] :
    Group.IsSolvable (borel (K := F)) := by
  let : Group.IsSolvable (unipotent (K := F)) := isSolvable_unipotent
  let : Group.IsSolvable (splitTorus (K := F)) := isSolvable_splitTorus
  have hU : unipotent (K := F) ≤ borel := le_sup_left
  have hT : splitTorus (K := F) ≤ borel := le_sup_right
  let : Group.IsSolvable (unipotent.subgroupOf (borel (K := F))) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hU).toMonoidHom) (subgroupOfEquivOfLe hU).injective
  let : Group.IsSolvable (splitTorus.subgroupOf (borel (K := F))) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hT).toMonoidHom) (subgroupOfEquivOfLe hT).injective
  have hn : borel (K := F) ≤ normalizer (unipotent (K := F) : Set (Model F)) := by
    change unipotent ⊔ splitTorus ≤ normalizer (unipotent (K := F) : Set (Model F))
    exact sup_le (unipotent (K := F)).le_normalizer (le_normalizer_iff.mpr
      (fun _ ht _ hu => torus_normalizes_unipotent ht hu))
  let : (unipotent.subgroupOf (borel (K := F))).Normal :=
    normal_subgroupOf_of_le_normalizer hn
  apply Group.isSolvable_of_normal_sup_eq_top
    (unipotent.subgroupOf (borel (K := F))) (splitTorus.subgroupOf borel)
  rw [← subgroupOf_sup hU hT]
  exact subgroupOf_self _

end Atlas.G2.DerivedNormalizerSolvable
