module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.Basic

/-!
# Held core and candidate word certificate data

Each of the six nonidentity generators is a product of at most four
commutators with the two published odd generators. All identities are checked
on the full faithful degree-2058 representation. Relative normality gives the
reverse inclusion. This does not yet identify the word core with O₂(M).

Sources: GLS3 Table 5.3p; unchanged ATLAS max3/max4 words and permutations.
The discovered expressions are retained in source/witnesses.json; only the
kernel-checked identities below are used as proofs.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
open Held.TwoLocalCandidates

@[expose] def corePerm (i : Bool) (k : Fin 7) : Equiv.Perm (Fin 2058) :=
  if i then ![Cores.Tables1.p2, Cores.Tables1.p3, Cores.Tables1.p4, Cores.Tables1.p5,
    Cores.Tables1.p6, Cores.Tables1.p7, Cores.Tables1.p8] k
  else ![Cores.Tables0.p2, Cores.Tables0.p3, Cores.Tables0.p4, Cores.Tables0.p5,
    Cores.Tables0.p6, Cores.Tables0.p7, Cores.Tables0.p8] k

theorem representation_coreGenerator (i : Bool) (k : Fin 7) :
    representation (coreGenerator i k).val = corePerm i k := by
  cases i <;> fin_cases k
  · exact Cores.Tables0.p2_eq.symm
  · exact Cores.Tables0.p3_eq.symm
  · exact Cores.Tables0.p4_eq.symm
  · exact Cores.Tables0.p5_eq.symm
  · exact Cores.Tables0.p6_eq.symm
  · exact Cores.Tables0.p7_eq.symm
  · exact Cores.Tables0.p8_eq.symm
  · exact Cores.Tables1.p2_eq.symm
  · exact Cores.Tables1.p3_eq.symm
  · exact Cores.Tables1.p4_eq.symm
  · exact Cores.Tables1.p5_eq.symm
  · exact Cores.Tables1.p6_eq.symm
  · exact Cores.Tables1.p7_eq.symm
  · exact Cores.Tables1.p8_eq.symm

@[expose] def oddPerm (i : Bool) (j k : Fin 2) : Equiv.Perm (Fin 2058) :=
  match i, j, k with
  | false, 0, 0 => LocalActions.RepresentativeImages.Pair00.odd0
  | false, 0, 1 => LocalActions.RepresentativeImages.Pair00.odd1
  | false, 1, 0 => LocalActions.RepresentativeImages.Pair01.odd0
  | false, 1, 1 => LocalActions.RepresentativeImages.Pair01.odd1
  | true, 0, 0 => LocalActions.RepresentativeImages.Pair10.odd0
  | true, 0, 1 => LocalActions.RepresentativeImages.Pair10.odd1
  | true, 1, 0 => LocalActions.RepresentativeImages.Pair11.odd0
  | true, 1, 1 => LocalActions.RepresentativeImages.Pair11.odd1

theorem representation_oddGenerator (i : Bool) (j k : Fin 2) :
    representation (oddGenerator i j k).val = oddPerm i j k := by
  cases i <;> fin_cases j <;> fin_cases k
  · exact LocalActions.RepresentativeImages.Pair00.odd0_eq.symm
  · exact LocalActions.RepresentativeImages.Pair00.odd1_eq.symm
  · exact LocalActions.RepresentativeImages.Pair01.odd0_eq.symm
  · exact LocalActions.RepresentativeImages.Pair01.odd1_eq.symm
  · exact LocalActions.RepresentativeImages.Pair10.odd0_eq.symm
  · exact LocalActions.RepresentativeImages.Pair10.odd1_eq.symm
  · exact LocalActions.RepresentativeImages.Pair11.odd0_eq.symm
  · exact LocalActions.RepresentativeImages.Pair11.odd1_eq.symm

@[expose] def commutatorWord : Bool → Fin 2 → Fin 7 → List (Fin 7 × Fin 2)
  | false, 0, 0 => [(0, 0), (3, 1), (5, 0)]
  | false, 0, 1 => [(5, 0)]
  | false, 0, 2 => [(0, 1), (1, 0)]
  | false, 0, 3 => [(2, 0), (5, 0)]
  | false, 0, 4 => [(2, 1), (5, 0)]
  | false, 0, 5 => [(1, 0), (5, 0)]
  | false, 1, 0 => [(0, 0), (0, 1)]
  | false, 1, 1 => [(1, 0), (5, 0)]
  | false, 1, 2 => [(1, 0), (3, 0)]
  | false, 1, 3 => [(1, 0), (2, 1)]
  | false, 1, 4 => [(0, 1), (5, 1)]
  | false, 1, 5 => [(1, 0)]
  | true, 0, 0 => [(0, 0), (1, 0), (5, 0)]
  | true, 0, 1 => [(2, 1), (4, 0), (5, 0)]
  | true, 0, 2 => [(3, 1)]
  | true, 0, 3 => [(2, 1), (3, 1)]
  | true, 0, 4 => [(0, 0), (1, 0)]
  | true, 0, 5 => [(1, 0), (1, 1), (4, 0), (5, 0)]
  | true, 1, 0 => [(0, 1), (5, 0)]
  | true, 1, 1 => [(0, 0), (5, 1)]
  | true, 1, 2 => [(3, 0)]
  | true, 1, 3 => [(0, 0), (3, 1)]
  | true, 1, 4 => [(0, 1), (3, 0), (4, 0)]
  | true, 1, 5 => [(3, 0), (5, 1)]
  | _, _, _ => []

@[expose] def twoWord : Bool → Fin 2 → Fin 7 → List (Fin 4 × ℤ)
  | false, 0, 0 => [(3, -1), (0, -1), (2, -1), (3, -1), (1, -1), (2, -1), (0, -1), (3, -1), (2, -1), (1, -1), (2, -1)]
  | false, 0, 1 => [(2, 1), (1, 1), (2, 1), (3, 1), (2, -1), (1, -1), (3, -1), (2, -1)]
  | false, 0, 2 => [(3, -1), (0, -1), (1, 1), (2, 1), (3, 1), (1, 1), (2, 1), (3, -1), (2, -1), (0, -1), (2, -1)]
  | false, 0, 3 => [(3, -1), (0, -1), (1, -1), (3, -1), (2, -1), (1, -1), (2, -1), (3, -1), (2, -1), (0, -1), (2, -1)]
  | false, 0, 4 => [(0, -1), (2, 1), (0, 1), (2, 1), (3, 1), (2, -1), (1, -1), (3, -1), (2, -1), (1, -1)]
  | false, 0, 5 => [(0, -1), (2, 1), (0, 1), (2, 1), (3, 1), (1, -1), (3, -1), (2, -1), (3, -1), (1, -1), (2, -1)]
  | false, 1, 0 => [(3, -1), (2, 1), (0, -1), (2, -1), (0, -1)]
  | false, 1, 1 => [(3, -1), (1, -1), (3, -1), (1, -1), (2, 1), (0, -1), (2, -1), (0, -1)]
  | false, 1, 2 => [(3, -1), (1, -1), (3, -1), (1, -1), (0, -1), (3, -1), (0, -1)]
  | false, 1, 3 => [(3, -1), (1, -1), (3, -1), (1, -1), (0, 1), (2, 1), (3, 1), (2, -1), (0, -1)]
  | false, 1, 4 => [(1, 1), (3, 1), (0, -1), (3, -1), (1, -1), (0, -1)]
  | false, 1, 5 => [(0, 1), (2, 1), (3, 1), (0, 1), (2, -1), (2, -1), (2, -1)]
  | true, 0, 0 => [(0, -1), (1, 1), (3, 1), (0, 1), (3, 1), (1, -1), (2, -1), (3, -1), (2, -1)]
  | true, 0, 1 => [(0, -1), (1, -1), (3, -1), (1, -1), (0, -1), (2, -1), (3, -1), (2, -1), (3, -1)]
  | true, 0, 2 => [(1, 1), (3, 1), (1, 1), (2, 1), (3, -1), (2, -1)]
  | true, 0, 3 => [(0, -1), (1, 1), (3, 1), (2, 1), (3, 1), (0, -1), (3, -1), (1, -1), (2, -1), (3, -1)]
  | true, 0, 4 => [(1, 1), (2, 1), (3, 1), (2, 1), (1, -1), (3, -1)]
  | true, 0, 5 => [(0, -1), (1, 1), (3, 1), (2, 1), (3, 1), (0, -1), (3, -1), (1, -1), (2, -1)]
  | true, 1, 0 => [(2, -1), (1, -1), (2, -1), (0, -1), (2, 1), (3, 1), (1, 1), (3, 1), (0, -1), (3, -1), (2, -1), (3, -1)]
  | true, 1, 1 => [(2, -1), (1, -1), (2, -1), (0, -1), (3, -1), (2, -1), (1, -1), (3, -1), (0, -1), (3, -1), (2, -1), (3, -1)]
  | true, 1, 2 => [(2, -1), (3, -1), (2, -1)]
  | true, 1, 3 => [(0, -1), (3, -1), (2, -1), (0, -1), (3, -1), (2, -1)]
  | true, 1, 4 => [(3, -1)]
  | true, 1, 5 => [(1, -1), (2, -1), (3, -1), (2, -1), (1, -1)]
  | _, _, _ => []


end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
