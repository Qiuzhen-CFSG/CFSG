module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.Criterion
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables
import Mathlib.Tactic.FinCases

/-!
# Checked permutation evaluators for Held extension certificates

Reuse the certified lookup permutations of `TwoGroup.Tables` to evaluate the
unchanged representative words. The polycyclic tables are indexed in reverse
order there; the formula below preserves the original least-significant-bit
normal-form convention. Every evaluator is proved equal to the actual action.

This is a computational interface for the finite node and branch certificates,
not a coverage or subgroup enumeration assertion.
Source: the ATLAS HeG1-p2058B0 words and the checked tables in `TwoGroup.Tables`.
-/

@[expose] public section

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks
open LocalPairs.SylowGeometry.Calculations
open LocalPairs.SylowGeometry.Calculations.TwoGroup
open LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables

def generatorAction : Fin 4 → Equiv.Perm (Fin 2058)
  | 0 => g0
  | 1 => g1
  | 2 => g2
  | _ => g3

theorem generatorAction_eq (k : Fin 4) : generatorAction k = representation (generator k) := by
  fin_cases k
  · exact g0_eq
  · exact g1_eq
  · exact g2_eq
  · exact g3_eq

def letterAction (k : ℤ) : Equiv.Perm (Fin 2058) :=
  let x := generatorAction (Fin.ofNat 4 (k.natAbs - 1))
  if k < 0 then x⁻¹ else x

theorem letterAction_eq (k : ℤ) : letterAction k = representation (letter k).val := by
  simp only [letterAction, letter, generatorAction_eq]
  split <;> rfl

def wordAction (w : List ℤ) : Equiv.Perm (Fin 2058) := (w.map letterAction).prod

theorem wordAction_eq (w : List ℤ) : wordAction w = representation (word w).val := by
  change _ = (representation.comp representative.subtype) (word w)
  simp only [wordAction, word, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact letterAction_eq k

def normalFormAction (n : Fin 1024) : Equiv.Perm (Fin 2058) :=
  ((List.finRange 10).map (fun i =>
    pcTable ⟨9 - i.val, by omega⟩ ^ (n.val / 2 ^ i.val % 2))).prod

private theorem literalWord_pcGenerator (i : Fin 10) :
    (word (pcWord i)).val = pcGenerator ⟨9 - i.val, by omega⟩ := by
  fin_cases i <;> simp [word, letter, pcWord, pcGenerator, mul_assoc] <;> rfl

theorem normalFormAction_eq (n : Fin 1024) :
    normalFormAction n = representation (normalForm n).val := by
  change _ = (representation.comp representative.subtype) (normalForm n)
  simp only [normalFormAction, normalForm, map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, map_pow, MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [pcTable_eq, literalWord_pcGenerator]

/-- Equality of two permutations on the certified four-point base. -/
def sameAction (x y : Equiv.Perm (Fin 2058)) : Bool :=
  decide (∀ k : Fin 4, x ⟨k.val, by omega⟩ = y ⟨k.val, by omega⟩)

def memberAction (i : Option (Fin 22)) (x : Equiv.Perm (Fin 2058)) : Bool :=
  (members i).any (fun m => sameAction x (normalFormAction m))

def cosetAction (i : Option (Fin 22)) (n : Fin 1024)
    (x : Equiv.Perm (Fin 2058)) : Bool :=
  memberAction i x || memberAction i (normalFormAction n * x)

def squareAction (n : Fin 1024) : Bool :=
  sameAction (normalFormAction n * normalFormAction n) 1

def commuteAction (i : Option (Fin 22)) (n : Fin 1024) : Bool :=
  (rowGenerators i).all (fun w =>
    sameAction (normalFormAction n * wordAction w) (wordAction w * normalFormAction n))

def conjugateAction (i : Option (Fin 22)) (n : Fin 1024) : Bool :=
  (List.finRange 4).all (fun k =>
    cosetAction i n ((generatorAction k)⁻¹ * normalFormAction n * generatorAction k))

def acceptedAction (i : Option (Fin 22)) (n : Fin 1024) (j : Option (Fin 22)) : Bool :=
  memberAction j (normalFormAction n) &&
    (rowGenerators i).all (fun w => memberAction j (wordAction w)) &&
    (rowGenerators j).all (fun w => cosetAction i n (wordAction w))

/-- The same branch checker evaluated using previously certified lookup permutations. -/
def branchAction (i : Option (Fin 22)) (n : Fin 1024) : Bool :=
  !squareAction n || !commuteAction i n || !conjugateAction i n ||
    acceptedAction i n (target i n)

theorem branchAction_eq (i : Option (Fin 22)) (n : Fin 1024) :
    branchAction i n = branchCheck i n := by
  simp only [branchAction, branchCheck, squareAction, squareCheck,
    commuteAction, commuteCheck, conjugateAction, conjugateCheck,
    acceptedAction, acceptedCheck, cosetAction, cosetCheck, memberAction,
    memberCheck, sameAction, same, normalFormAction_eq, wordAction_eq,
    generatorAction_eq, Subgroup.coe_mul, Subgroup.coe_one, Subgroup.coe_inv,
    map_mul, map_one, map_inv]

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks
