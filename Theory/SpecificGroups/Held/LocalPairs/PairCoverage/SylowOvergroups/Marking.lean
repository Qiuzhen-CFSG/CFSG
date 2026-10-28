module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalSubgroups

/-!
# A common marking for the two Held local subgroups

The four marked elements are words in the first literal ATLAS local subgroup.
The alignment word and the alternative expressions in the second subgroup
are search data. Their equality on all 2058 points remains to be checked.
No Sylow order, two-group property, or exhaustive coverage is asserted here.

Sources: ATLAS HeG1-max3W1 and HeG1-max4W1, as translated in
`LocalSubgroups`; the reproducible search data are in `source/marking.json`.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.SylowOvergroups
open Subgroup

set_option maxRecDepth 4096

/-- A word with signed powers; the first letter selects x, the second y. -/
def wordEval {G : Type*} [Group G] (x y : G) : List (Bool × ℤ) → G
  | [] => 1
  | (i, n) :: w => (if i then y else x) ^ n * wordEval x y w

theorem wordEval_mem {G : Type*} [Group G] (H : Subgroup G)
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) (w : List (Bool × ℤ)) :
    wordEval x y w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons v w ih =>
    exact H.mul_mem (H.zpow_mem (by cases v.1 <;> assumption) _) ih

theorem map_wordEval {G H : Type*} [Group G] [Group H] (f : G →* H)
    (x y : G) (w : List (Bool × ℤ)) :
    f (wordEval x y w) = wordEval (f x) (f y) w := by
  induction w with
  | nil => exact f.map_one
  | cons v w ih =>
    rcases v with ⟨i, n⟩
    cases i <;> simp [wordEval, map_mul, map_zpow, ih]

/-- The conjugator is an actual word in the existing Held generators. -/
def alignment : He := wordEval a b [(false, -1), (true, -2), (false, -1), (true, 2), (false, -1), (true, -2), (false, -1), (true, 2), (false, -1), (true, -1), (false, -1), (true, 3), (false, -1), (true, 1), (false, -1), (true, 1), (false, -1), (true, -1), (false, -1), (true, -2), (false, -1), (true, -2), (false, -1), (true, 1), (false, -1), (true, -1), (false, -1), (true, -1), (false, -1), (true, -1), (false, -1), (true, -1), (false, -1), (true, -2), (false, -1), (true, -3), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 2), (false, 1), (true, 3), (false, 1), (true, 1), (false, 1), (true, -2), (false, -1), (true, -3), (false, -1), (true, -1), (false, -1), (true, -1), (false, -3), (true, -2), (false, -1), (true, -3), (false, -1), (true, 3), (false, -1), (true, -3), (false, -1), (true, -2)]

/-- Four words in the first local subgroup. -/
def generatorWords : Fin 4 → List (Bool × ℤ)
  | 0 => [(false, -1), (true, 3), (false, -1), (true, -1), (false, -1), (true, -1), (false, -1), (true, 1), (false, -1), (true, 1), (false, -1), (true, -3), (false, -1), (true, -1), (false, -1), (true, -2), (false, -1), (true, -1), (false, -1), (true, -1), (false, -1)]
  | 1 => [(false, -1), (true, 1), (false, -1), (true, 1), (false, 1), (true, -2), (false, 1), (true, -4), (false, 1), (true, -3), (false, -1), (true, 1), (false, -1), (true, -1), (false, -1), (true, 1)]
  | 2 => [(false, -1), (true, -2), (false, -1), (true, -2), (false, -1), (true, -3), (false, -1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 2), (false, 1), (true, 1)]
  | 3 => [(false, -1), (true, -1), (false, -1), (true, -3), (false, -1), (true, 2), (false, -1), (true, -1), (false, -1), (true, -2), (false, 1), (true, 2), (false, 1), (true, 2)]

/-- Expressions for their conjugates in the second local subgroup. -/
def secondWords : Fin 4 → List (Bool × ℤ)
  | 0 => [(true, 2), (false, 1), (true, -2), (false, 1), (true, -1), (false, 1), (true, -2), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, -1), (true, -1), (false, -1), (true, -4)]
  | 1 => [(true, 3), (false, 1), (true, -2), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 2), (false, 1), (true, 4), (false, -1), (true, -5), (false, -1), (true, -2)]
  | 2 => [(true, -1), (false, -1), (true, 2), (false, -1), (true, -5), (false, -1), (true, 1), (false, -1), (true, -5), (false, -1), (true, -2)]
  | 3 => [(false, -1), (true, -3), (false, -1), (true, -1), (false, -1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -3), (false, -1), (true, -5), (false, -1), (true, -3)]

def markedGenerator (i : Fin 4) : He :=
  wordEval a (localWord false) (generatorWords i)

/-- A concrete subgroup; its two-group property is a separate obligation. -/
def markedSubgroup : Subgroup He := closure (Set.range markedGenerator)

/-- The two candidates with the second one aligned by the specified word. -/
def alignedOvergroup : Bool → Subgroup He
  | false => localOvergroup false
  | true => (localOvergroup true).comap (MulAut.conj alignment).toMonoidHom

theorem markedGenerator_mem (i : Fin 4) : markedGenerator i ∈ markedSubgroup :=
  subset_closure ⟨i, rfl⟩

theorem markedSubgroup_le_first : markedSubgroup ≤ alignedOvergroup false := by
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact wordEval_mem _ (a_mem_localOvergroup false)
    (localWord_mem_localOvergroup false) (generatorWords i)

/-- Each candidate is an actual conjugate of its original ATLAS subgroup. -/
theorem alignedOvergroup_map (i : Bool) :
    (alignedOvergroup i).map
      (MulAut.conj (if i then alignment else 1)).toMonoidHom = localOvergroup i := by
  cases i
  · change (localOvergroup false).map (MonoidHom.id He) = localOvergroup false
    exact map_id _
  · exact map_comap_eq_self_of_surjective
      (f := (MulAut.conj alignment).toMonoidHom)
      (MulAut.conj alignment).surjective _

end Held.LocalPairs.PairCoverage.SylowOvergroups
