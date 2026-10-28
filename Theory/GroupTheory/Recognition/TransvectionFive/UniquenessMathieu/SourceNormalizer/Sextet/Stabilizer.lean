module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Kernel
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases

/-!
# The S₅ stabilizer in the exceptional six-point geometry

A nonzero exceptional vector lies in a unique four-group. Its stabilizer acts
faithfully on the other five four-groups, since the six-point kernel fixes no
nonzero vector. Its orbit has at most 18 elements. When the symmetry group
has order 2160, orbit–stabilizer forces this faithful five-point action onto S₅.
The ambient normalizer supplies that group order in the source application.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4(2), p.218.
-/

public noncomputable section
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
open UniquenessLinear.PlaneCensus (Code)

abbrev pointFixer (x : Code) := MulAction.stabilizer symmetryGroup x

private theorem fixer_line (x : Code) (hx : exceptional x = true) (i : Fin 6)
    (hi : x ∈ line i) (f : pointFixer x) : action f.val i = i := by
  obtain ⟨j, _, hu⟩ := exceptional_unique_line x hx
  have hfix : f.val.val x = x := f.property
  have hm := (action_mem_line f.val i x).mpr hi
  rw [hfix] at hm
  exact (hu _ hm).trans (hu i hi).symm

/-- The literal action of an exceptional vector stabilizer on the other five
four-groups. -/
def fiveAction (x : Code) (hx : exceptional x = true) (i : Fin 6) (hi : x ∈ line i) :
    pointFixer x →* Equiv.Perm {j : Fin 6 // j ≠ i} where
  toFun f := (action f.val).subtypePerm (fun j => by
    conv_lhs => rw [← fixer_line x hx i hi f]
    exact (action f.val).injective.eq_iff.not)
  map_one' := by apply Equiv.ext; intro j; apply Subtype.ext; exact congrArg (fun e : Equiv.Perm (Fin 6) => e j) action.map_one
  map_mul' f g := by
    apply Equiv.ext
    intro j
    apply Subtype.ext
    exact congrArg (fun e : Equiv.Perm (Fin 6) => e j) (action.map_mul f.val g.val)

theorem fiveAction_injective (x : Code) (hx : exceptional x = true) (i : Fin 6)
    (hi : x ∈ line i) : Function.Injective (fiveAction x hx i hi) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro f hf
  have he : action f.val = 1 := by
    apply Equiv.ext
    intro j
    by_cases hj : j = i
    · subst j
      exact fixer_line x hx i hi f
    · exact congrArg (fun p : Equiv.Perm {j : Fin 6 // j ≠ i} => (p ⟨j,hj⟩).val) hf
  have hk := kernel_fix_nonzero (⟨f.val, he⟩ : action.ker) x
    (exceptional_nonzero x hx) f.property
  exact Subtype.ext (congrArg (fun k : action.ker => k.val) hk)

private theorem remaining_card (i : Fin 6) : Fintype.card {j : Fin 6 // j ≠ i} = 5 := by
  fin_cases i <;> decide

private theorem fivePerm_card (i : Fin 6) : Nat.card (Equiv.Perm {j : Fin 6 // j ≠ i}) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, remaining_card]
  decide

private theorem exceptional_orbit_bound (x : Code) (hx : exceptional x = true) :
    Nat.card (MulAction.orbit symmetryGroup x) ≤ 18 := by
  let ev : MulAction.orbit symmetryGroup x → {y : Code // exceptional y = true} := fun y =>
    ⟨y.val, by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp y.property
      rw [← hg]
      exact ((mem_symmetryGroup _).mp g.property).2 x |>.trans hx⟩
  have hi : Function.Injective ev := by
    intro a b h
    exact Subtype.ext (show a.val = b.val from congrArg (fun y : {y : Code // exceptional y = true} => y.val) h)
  have hc := Nat.card_le_card_of_injective ev hi
  have he : Nat.card {y : Code // exceptional y = true} = 18 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact he ▸ hc

theorem fiveAction_bijective (hcard : Nat.card symmetryGroup = 2160)
    (x : Code) (hx : exceptional x = true) (i : Fin 6) (hi : x ∈ line i) :
    Function.Bijective (fiveAction x hx i hi) := by
  apply (fiveAction_injective x hx i hi).bijective_of_nat_card_le
  rw [fivePerm_card]
  have ho := exceptional_orbit_bound x hx
  have hm := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup symmetryGroup x)
  rw [Nat.card_prod, hcard] at hm
  have hle := Nat.mul_le_mul_right (Nat.card (pointFixer x)) ho
  rw [hm] at hle
  omega

/-- The exceptional vector stabilizer is S₅, by its actual action on the
remaining five four-groups. -/
def pointFixerEquiv (hcard : Nat.card symmetryGroup = 2160)
    (x : Code) (hx : exceptional x = true) (i : Fin 6) (hi : x ∈ line i) :
    pointFixer x ≃* Equiv.Perm (Fin 5) :=
  (MulEquiv.ofBijective (fiveAction x hx i hi) (fiveAction_bijective hcard x hx i hi)).trans
    (Fintype.equivOfCardEq (show Fintype.card {j : Fin 6 // j ≠ i} = Fintype.card (Fin 5) by
      rw [remaining_card, Fintype.card_fin])).permCongrHom

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
