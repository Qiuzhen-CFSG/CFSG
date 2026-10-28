module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.TwoTables00
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.TwoTables01
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.TwoTables10
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.TwoTables11

/-!
# Membership of the Held kernel envelope in both literal pairs

Short products of the four published two-generators recover every word-core
generator. The distinguished cube-one element differs from a generator of the
second odd candidate by a checked core word. These certificates prove envelope
containment without orders or a Sylow hypothesis. They do not assert that the
envelope exhausts the native action kernel.

Sources: GLS3 Table 5.3p; ATLAS max3/max4 and degree-2058 data. The original
membership discovery expressions are retained in source/witnesses.json.
-/

public section
open Subgroup
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
open Held.TwoLocalCandidates

@[expose] def twoPerm (i : Bool) (j : Fin 2) (k : Fin 4) : Equiv.Perm (Fin 2058) :=
  match i, j, k with
  | false, 0, 0 => TwoTables00.p0
  | false, 0, 1 => TwoTables00.p1
  | false, 0, 2 => TwoTables00.p2
  | false, 0, 3 => TwoTables00.p3
  | false, 1, 0 => TwoTables01.p0
  | false, 1, 1 => TwoTables01.p1
  | false, 1, 2 => TwoTables01.p2
  | false, 1, 3 => TwoTables01.p3
  | true, 0, 0 => TwoTables10.p0
  | true, 0, 1 => TwoTables10.p1
  | true, 0, 2 => TwoTables10.p2
  | true, 0, 3 => TwoTables10.p3
  | true, 1, 0 => TwoTables11.p0
  | true, 1, 1 => TwoTables11.p1
  | true, 1, 2 => TwoTables11.p2
  | true, 1, 3 => TwoTables11.p3

theorem representation_twoGenerator (i : Bool) (j : Fin 2) (k : Fin 4) :
    representation (twoGenerator i j k).val = twoPerm i j k := by
  cases i <;> fin_cases j <;> fin_cases k
  · exact TwoTables00.p0_eq.symm
  · exact TwoTables00.p1_eq.symm
  · exact TwoTables00.p2_eq.symm
  · exact TwoTables00.p3_eq.symm
  · exact TwoTables01.p0_eq.symm
  · exact TwoTables01.p1_eq.symm
  · exact TwoTables01.p2_eq.symm
  · exact TwoTables01.p3_eq.symm
  · exact TwoTables10.p0_eq.symm
  · exact TwoTables10.p1_eq.symm
  · exact TwoTables10.p2_eq.symm
  · exact TwoTables10.p3_eq.symm
  · exact TwoTables11.p0_eq.symm
  · exact TwoTables11.p1_eq.symm
  · exact TwoTables11.p2_eq.symm
  · exact TwoTables11.p3_eq.symm

theorem twoWord_spec (i : Bool) (j : Fin 2) (k : Fin 7) :
    ((twoWord i j k).map (fun t => (twoGenerator i j t.1).val ^ t.2)).prod =
      (coreGenerator i k).val := by
  cases i <;> fin_cases j
  · exact TwoTables00.coreWord_spec k
  · exact TwoTables01.coreWord_spec k
  · exact TwoTables10.coreWord_spec k
  · exact TwoTables11.coreWord_spec k

theorem ambientWordCore_le_candidateTwo (i : Bool) (j : Fin 2) :
    ambientWordCore i ≤ LocalActions.candidateTwo i j := by
  rw [ambientWordCore_eq_closure]
  apply (closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  change (coreGenerator i k).val ∈ _
  rw [← twoWord_spec i j k]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
  exact (LocalActions.candidateTwo i j).zpow_mem (subset_closure (Set.mem_range_self t.1)) t.2

@[expose] def thirdCorrection (i : Bool) : List (Fin 7) :=
  if i then [3, 4] else [0, 1, 2, 4]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
theorem kernelThird_correction (i : Bool) :
    (kernelThird i).val =
      ((thirdCorrection i).map (fun k => (coreGenerator i k).val)).prod *
        (oddGenerator i 1 0).val ^ (if i then 1 else 2 : ℕ) := by
  apply representation_injective
  have hthird : representation (kernelThird i).val =
      if i then oddPerm i 0 0 * oddPerm i 0 1 else oddPerm i 0 0 := by
    simp only [kernelThird]
    split <;> simp only [Subgroup.coe_mul, map_mul, representation_oddGenerator]
  simp only [map_mul, map_pow, map_list_prod, List.map_map, Function.comp_def,
    representation_coreGenerator, representation_oddGenerator, hthird]
  cases i <;> apply Equiv.ext <;> apply Cores.allLetters <;> decide +kernel

theorem kernelThird_mem_pairProduct (i : Bool) (j : Fin 2) :
    kernelThird i ∈ (pairProduct i j).subgroupOf (localOvergroup i) := by
  have ho (k : Fin 2) : (oddGenerator i j k).val ∈ pairProduct i j :=
    (show LocalActions.candidateOdd i j ≤ pairProduct i j from le_sup_left)
      (LocalActions.RepresentativeImages.oddGenerator_mem i j k)
  fin_cases j
  · change (kernelThird i).val ∈ pairProduct i 0
    simp only [kernelThird]
    cases i
    · exact ho 0
    · simp only [↓reduceIte, Subgroup.coe_mul]
      exact (pairProduct true 0).mul_mem (ho 0) (ho 1)
  · change (kernelThird i).val ∈ pairProduct i 1
    rw [kernelThird_correction]
    apply (pairProduct i 1).mul_mem _ ((pairProduct i 1).pow_mem (ho 0) _)
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    exact (show LocalActions.candidateTwo i 1 ≤ pairProduct i 1 from le_sup_right)
      (ambientWordCore_le_candidateTwo i 1 ⟨coreGenerator i k, coreGenerator_mem i k, rfl⟩)

theorem kernelEnvelope_le_pairProduct (i : Bool) (j : Fin 2) :
    kernelEnvelope i ≤ (pairProduct i j).subgroupOf (localOvergroup i) := by
  apply sup_le _ (zpowers_le.mpr (kernelThird_mem_pairProduct i j))
  intro x hx
  exact (show LocalActions.candidateTwo i j ≤ pairProduct i j from le_sup_right)
    (ambientWordCore_le_candidateTwo i j ⟨x, hx, rfl⟩)

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
