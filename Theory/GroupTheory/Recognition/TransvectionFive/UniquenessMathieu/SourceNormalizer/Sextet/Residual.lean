module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Quintic
public import Theory.GroupTheory.SolvableResidual
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# The residual-fixed subgroup in the six-line representation

The exceptional vector stabilizer is S₅. Its perfect residual acts trivially
on the invariant four-element line, because S₄ is solvable. Conversely, the
specified quintic symmetry belongs to that residual (its S₅ image is even)
and fixes exactly the line. This identifies the complete fixed set, which
is transported to the original centralizer in `ResidualFour`.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4(2), p.218.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
open UniquenessLinear.PlaneCensus (Code)

private theorem fixer_line (x : Code) (hx : exceptional x = true) (i : Fin 6)
    (hi : x ∈ line i) (f : pointFixer x) : action f.val i = i := by
  obtain ⟨j, _, hu⟩ := exceptional_unique_line x hx
  have hfix : f.val.val x = x := f.property
  have hm := (action_mem_line f.val i x).mpr hi
  rw [hfix] at hm
  exact (hu _ hm).trans (hu i hi).symm

private def lineAction (x : Code) (hx : exceptional x = true) (i : Fin 6)
    (hi : x ∈ line i) : pointFixer x →* Equiv.Perm {y : Code // y ∈ line i} where
  toFun f := f.val.val.subtypePerm (fun y => by
    have h := action_mem_line f.val i y
    rwa [fixer_line x hx i hi f] at h)
  map_one' := by ext y; rfl
  map_mul' f g := by ext y; rfl

private theorem residual_fixes_line (x : Code) (hx : exceptional x = true) (i : Fin 6)
    (hi : x ∈ line i) (f : pointFixer x) (hf : f ∈ solvableResidual (pointFixer x))
    (y : Code) (hy : y ∈ line i) : f.val.val y = y := by
  classical
  let e : {y : Code // y ∈ line i} ≃ Fin 4 := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe, line_card])
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm {y : Code // y ∈ line i}) :=
    Group.isSolvable_of_isSolvable_injective (f := e.permCongrHom.toMonoidHom) e.permCongrHom.injective
  have hm := map_solvableResidual_le (lineAction x hx i hi)
  rw [solvableResidual_eq_bot (G := Equiv.Perm {y : Code // y ∈ line i})] at hm
  have he : lineAction x hx i hi f = 1 := hm (mem_map_of_mem _ hf)
  exact congrArg (fun p : Equiv.Perm {y : Code // y ∈ line i} => (p ⟨y,hy⟩).val) he

private theorem perm_fifth_mem_residual (f : Equiv.Perm (Fin 5)) (hf : f ^ 5 = 1) :
    f ∈ solvableResidual (Equiv.Perm (Fin 5)) := by
  have hs : Equiv.Perm.sign f = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign f) with hs | hs
    · exact hs
    · have hh := congrArg Equiv.Perm.sign hf
      rw [map_pow, map_one, hs] at hh
      have hv := congrArg (fun u : ℤˣ => (u : ℤ)) hh
      norm_num at hv
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact le_solvableResidual_of_isPerfect _ (Equiv.Perm.mem_alternatingGroup.mpr hs)

private theorem quintic_mem_residual (hcard : Nat.card symmetryGroup = 2160)
    (x : Code) (hx : exceptional x = true) (i : Fin 6) (hi : x ∈ line i) :
    (⟨quintic i, (quintic_fixed_iff i x).mpr hi⟩ : pointFixer x) ∈
      solvableResidual (pointFixer x) := by
  let f : pointFixer x := ⟨quintic i, (quintic_fixed_iff i x).mpr hi⟩
  let e := pointFixerEquiv hcard x hx i hi
  have hf : f ^ 5 = 1 := Subtype.ext (quintic_pow i)
  have he : e f ∈ solvableResidual (Equiv.Perm (Fin 5)) :=
    perm_fifth_mem_residual (e f) (by rw [← map_pow, hf, map_one])
  rw [← map_solvableResidual_eq e.symm.toMonoidHom e.symm.surjective]
  exact ⟨e f, he, e.symm_apply_apply f⟩

/-- The residual of the exceptional vector stabilizer fixes exactly the
unique exceptional four-element line containing that vector. -/
theorem residual_fixed_iff (hcard : Nat.card symmetryGroup = 2160)
    (x : Code) (hx : exceptional x = true) (i : Fin 6) (hi : x ∈ line i) (y : Code) :
    (∀ f : pointFixer x, f ∈ solvableResidual (pointFixer x) → f.val.val y = y) ↔
      y ∈ line i := by
  constructor
  · intro hy
    exact (quintic_fixed_iff i y).mp
      (hy _ (quintic_mem_residual hcard x hx i hi))
  · intro hy f hf
    exact residual_fixes_line x hx i hi f hf y hy

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
