module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Definitions
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Fixed words for the Rudvalis local elementary-subgroup calculation

The four short words in the max4 generators fix a single subgroup `localP`.
The six further words give candidates arranged as a chain of four subgroups
with two overgroups of its last term. All are subgroups of the original
degree-4060 carrier, and the inclusions into `localP` and `max4` are proved.

GAP discovery suggests that `localP` is Sylow in max4 and that these are its
six nontrivial normal elementary abelian subgroups, of orders 2, 4, 8, 16,
32, and 32. This module asserts neither that classification nor those orders.
The separate local-cover certificates must establish the properties they use.

Source: the ATLAS programs attributed and preserved in
`SylowOvergroups.Definitions`. The local words are an independent finite-word
search in those generators; `source/Explore.g` reproduces the discovery on
the unchanged ATLAS permutation files. GAP output is not used as a proof.
The intended application is the Sylow-overgroup analysis cited in
Aschbacher--Smith, printed p.511 (PDF p.528), and GLS3 Table 5.3r.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover

private theorem fourWords_mem {G : Type*} [Group G] (H : Subgroup G)
    (x y : G) (hx : x ∈ H) (hy : y ∈ H) (i : Fin 4) :
    (![y * x * y⁻¹,
      x * y * x * y⁻¹ * x,
      y⁻¹ * x * y⁻¹ * x * y * x * y,
      x * y⁻¹ * x * y * x * y * x * y⁻¹ * x * y] : Fin 4 → G) i ∈ H := by
  fin_cases i <;> dsimp
  all_goals repeat first | exact hx | exact hy | apply H.mul_mem | apply H.inv_mem

/-- Four short words in the preserved max4 generator pair. -/
@[expose] public def localGenerators : Fin 4 → Model :=
  let x := max4Generators.1
  let y := max4Generators.2
  ![y * x * y⁻¹,
    x * y * x * y⁻¹ * x,
    y⁻¹ * x * y⁻¹ * x * y * x * y,
    x * y⁻¹ * x * y * x * y * x * y⁻¹ * x * y]

/-- The fixed subgroup for the intrinsic Sylow and elementary calculations. -/
@[expose] public def localP : Subgroup Model :=
  Subgroup.closure (Set.range localGenerators)

public theorem localGenerators_mem (i : Fin 4) : localGenerators i ∈ localP :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- The fixed subgroup lies in the actual fourth ATLAS candidate. -/
public theorem localP_le_max4 : localP ≤ max4 := by
  have hx : max4Generators.1 ∈ max4 := Subgroup.subset_closure (by simp)
  have hy : max4Generators.2 ∈ max4 := Subgroup.subset_closure (by simp)
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact fourWords_mem max4 _ _ hx hy i

/-- Letters 0--3 are the four fixed generators; 4--7 are their inverses. -/
@[expose] public def localLetter : Fin 8 → Model :=
  ![localGenerators 0, localGenerators 1, localGenerators 2, localGenerators 3,
    (localGenerators 0)⁻¹, (localGenerators 1)⁻¹,
    (localGenerators 2)⁻¹, (localGenerators 3)⁻¹]

/-- Evaluate a word without reversing the ATLAS multiplication convention. -/
@[expose] public def localWord (w : List (Fin 8)) : Model :=
  (w.map localLetter).prod

public theorem localWord_mem (w : List (Fin 8)) : localWord w ∈ localP := by
  apply Subgroup.list_prod_mem
  intro z hz
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
  fin_cases i
  · exact localGenerators_mem 0
  · exact localGenerators_mem 1
  · exact localGenerators_mem 2
  · exact localGenerators_mem 3
  · exact localP.inv_mem (localGenerators_mem 0)
  · exact localP.inv_mem (localGenerators_mem 1)
  · exact localP.inv_mem (localGenerators_mem 2)
  · exact localP.inv_mem (localGenerators_mem 3)

/-- Words for a common chain basis and the two final branches. -/
@[expose] public def elementaryWords : Fin 6 → List (Fin 8) :=
  ![[4, 5, 7, 5, 7, 4, 3, 5, 4, 3, 5, 3, 4, 7],
    [4, 5, 3, 4, 7, 4, 3, 4, 7, 5],
    [4, 6, 5, 7, 6, 5, 4, 7],
    [4, 6, 5, 3, 5, 6, 4, 3, 4],
    [4, 3, 5, 3, 4, 7, 5, 7],
    [5, 3, 5, 3, 4, 7, 5, 3, 3, 6, 5, 4, 7, 6]]

/-- The six marked elements, as actual elements of Rudvalis.Model. -/
@[expose] public def elementaryGenerator (i : Fin 6) : Model :=
  localWord (elementaryWords i)

/-- Six generated candidates; their elementary nature and completeness are
separate proof obligations, not consequences of this definition. -/
@[expose] public def elementary : Fin 6 → Subgroup Model :=
  let c := elementaryGenerator
  ![Subgroup.closure {c 0},
    Subgroup.closure {c 0, c 1},
    Subgroup.closure {c 0, c 1, c 2},
    Subgroup.closure {c 0, c 1, c 2, c 3},
    Subgroup.closure {c 0, c 1, c 2, c 3, c 4},
    Subgroup.closure {c 0, c 1, c 2, c 3, c 5}]

/-- Every candidate is contained in the chosen fixed subgroup. -/
public theorem elementary_le_localP (i : Fin 6) : elementary i ≤ localP := by
  have hc (j : Fin 6) : elementaryGenerator j ∈ localP := localWord_mem _
  fin_cases i <;> apply (Subgroup.closure_le _).mpr <;> simp_all [Set.insert_subset_iff]

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
