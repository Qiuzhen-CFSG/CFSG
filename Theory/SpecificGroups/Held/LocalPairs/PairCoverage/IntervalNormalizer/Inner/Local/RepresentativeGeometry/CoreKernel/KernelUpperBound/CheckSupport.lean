module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.KernelUpperBound.Tables0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.KernelUpperBound.Tables1

/-!
# Representation bridges for the Held kernel relations

The finite checks use the already certified packed tables for the core,
the odd generators, and the five conjugate involutions.
Source: unchanged ATLAS degree-2058 data; GLS3 Table 5.3p.
-/

public section
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.KernelUpperBound
@[expose] def adjacentPerm (i : Bool) (k : Fin 5) : Equiv.Perm (Fin 2058) :=
  if i then ![Tables1.p0, Tables1.p1, Tables1.p2, Tables1.p3, Tables1.p4] k
  else ![Tables0.p0, Tables0.p1, Tables0.p2, Tables0.p3, Tables0.p4] k

theorem representation_adjacent_table (i : Bool) (k : Fin 5) :
    representation (adjacent i k).val = adjacentPerm i k := by
  cases i <;> fin_cases k
  · exact Tables0.p0_eq.symm
  · exact Tables0.p1_eq.symm
  · exact Tables0.p2_eq.symm
  · exact Tables0.p3_eq.symm
  · exact Tables0.p4_eq.symm
  · exact Tables1.p0_eq.symm
  · exact Tables1.p1_eq.symm
  · exact Tables1.p2_eq.symm
  · exact Tables1.p3_eq.symm
  · exact Tables1.p4_eq.symm

@[expose] def thirdPerm (i : Bool) : Equiv.Perm (Fin 2058) :=
  if i then oddPerm i 0 0 * oddPerm i 0 1 else oddPerm i 0 0

theorem representation_third (i : Bool) : representation (kernelThird i).val = thirdPerm i := by
  cases i <;> simp only [kernelThird, thirdPerm, Bool.false_eq_true, ↓reduceIte,
    Subgroup.coe_mul, map_mul, representation_oddGenerator]

theorem representation_correction (i : Bool) (w : List (Fin 7)) (e : Nat) :
    representation (correction i w e).val = (w.map (corePerm i)).prod * thirdPerm i ^ e := by
  simp only [correction, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.val_list_prod,
    map_mul, map_pow, map_list_prod, List.map_map, Function.comp_def,
    representation_coreGenerator, representation_third]

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.KernelUpperBound
