module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.Model
public import Theory.SpecificGroups.Held.Model.FourPointBase

/-!
# Evaluators for the five outer Held nodes

These finite lists retain exactly the published Pair00Two normal-form indices.
The checker tests squares, commutation, and all five conjugations, including the
outer actor. Accepted branches check both subgroup inclusions. No Boolean value
or discovery output is assumed true here.
Source: Aschbacher--Smith 15.3.41--42, printed p.1138; GLS3 Table 5.3p;
`ElementaryCatalogue/source/branch_discovery.json` and its reproducible script.
The unchanged ATLAS attribution is recorded in `Coverage/source/README.md`.
-/

@[expose] public section
open Subgroup Held Held.LocalPairs Held.LocalPairs.PairCoverage.LocalActions
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue.InnerExtensions
open RepresentativeImages Exhaustion.CandidateOrderCertificate.Factors

/-- Exact proposed membership lists, independently certified in Members. -/
def members : Option (Fin 4) → List (Fin 1024)
  | none => [0]
  | (some 0) => [0, 704]
  | (some 1) => [0, 704, 88, 664]
  | (some 2) => [0, 320, 704, 88, 664, 280, 984, 896]
  | (some 3) => [0, 320, 922, 704, 88, 642, 346, 664, 280, 962, 984, 896, 26, 66, 258, 730]

/-- Proposed accepted targets; omitted pairs must be rejected by the checker. -/
def transitions : Option (Fin 4) → List (Fin 1024 × Option (Fin 4))
  | none => [(0, none), (704, (some 0))]
  | (some 0) => [(0, (some 0)), (88, (some 1)), (664, (some 1)), (704, (some 0))]
  | (some 1) => [(0, (some 1)), (88, (some 1)), (280, (some 2)), (320, (some 2)), (664, (some 1)), (704, (some 1)), (896, (some 2)), (984, (some 2))]
  | (some 2) => [(0, (some 2)), (26, (some 3)), (66, (some 3)), (88, (some 2)), (258, (some 3)), (280, (some 2)), (320, (some 2)), (346, (some 3)), (642, (some 3)), (664, (some 2)), (704, (some 2)), (730, (some 3)), (896, (some 2)), (922, (some 3)), (962, (some 3)), (984, (some 2))]
  | (some 3) => [(0, (some 3)), (26, (some 3)), (66, (some 3)), (88, (some 3)), (258, (some 3)), (280, (some 3)), (320, (some 3)), (346, (some 3)), (642, (some 3)), (664, (some 3)), (704, (some 3)), (730, (some 3)), (896, (some 3)), (922, (some 3)), (962, (some 3)), (984, (some 3))]

def target (i : Option (Fin 4)) (n : Fin 1024) : Option (Fin 4) :=
  ((transitions i).find? (fun r => r.1 == n)).map Prod.snd |>.getD none

def rowGenerators : Option (Fin 4) → List (List ℤ)
  | none => []
  | some j => rowWords j

def letterAction (k : ℤ) : Equiv.Perm (Fin 2058) :=
  let x := Pair00Two.inputTable (Fin.ofNat 4 (k.natAbs - 1))
  if k < 0 then x⁻¹ else x

def wordAction (w : List ℤ) : Equiv.Perm (Fin 2058) := (w.map letterAction).prod

abbrev rho : pureTwo →* Equiv.Perm (Fin 2058) := representation.comp pureTwo.subtype

theorem input_eq (k : Fin 4) : Pair00Two.input k = (generator k).val := by
  fin_cases k <;> rfl

theorem letterAction_eq (k : ℤ) : letterAction k = rho (letter k) := by
  simp only [letterAction, letter, Pair00Two.inputTable_eq, input_eq]
  split <;> rfl

theorem wordAction_eq (w : List ℤ) : wordAction w = rho (word w) := by
  simp only [wordAction, word, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact letterAction_eq k

theorem normalTable_eq (n : Fin 1024) : Pair00Two.normalTable n = rho (pureElement n) :=
  Pair00Two.normalTable_eq n

/-- Equality on the established four-point base. -/
def same (x y : Equiv.Perm (Fin 2058)) : Bool :=
  decide (∀ k : Fin 4, x ⟨k.val, by omega⟩ = y ⟨k.val, by omega⟩)

theorem same_refl (x : Equiv.Perm (Fin 2058)) : same x x = true :=
  decide_eq_true (fun _ => rfl)

theorem same_rho {x y : pureTwo} : same (rho x) (rho y) = true ↔ x = y := by
  constructor
  · intro h
    exact Subtype.ext (Held.eq_of_four_point_images (of_decide_eq_true h))
  · rintro rfl
    exact same_refl _

def memberCheck (i : Option (Fin 4)) (x : Equiv.Perm (Fin 2058)) : Bool :=
  (members i).any (fun m => same x (Pair00Two.normalTable m))

def cosetCheck (i : Option (Fin 4)) (n : Fin 1024)
    (x : Equiv.Perm (Fin 2058)) : Bool :=
  memberCheck i x || memberCheck i (Pair00Two.normalTable n * x)

def squareCheck (n : Fin 1024) : Bool :=
  same (Pair00Two.normalTable n * Pair00Two.normalTable n) 1

def commuteCheck (i : Option (Fin 4)) (n : Fin 1024) : Bool :=
  (rowGenerators i).all (fun w =>
    same (Pair00Two.normalTable n * wordAction w) (wordAction w * Pair00Two.normalTable n))

/-- Exactly the four inner generators and the published outer actor. -/
def testAction : Fin 5 → Equiv.Perm (Fin 2058)
  | 0 => Pair00Two.inputTable 0
  | 1 => Pair00Two.inputTable 1
  | 2 => Pair00Two.inputTable 2
  | 3 => Pair00Two.inputTable 3
  | 4 => PureActors.Actor0.perm

theorem testAction_eq (k : Fin 5) : testAction k = (testLift k).val := by
  fin_cases k
  · exact Pair00Two.inputTable_eq 0
  · exact Pair00Two.inputTable_eq 1
  · exact Pair00Two.inputTable_eq 2
  · exact Pair00Two.inputTable_eq 3
  · rfl

def conjugateCheck (i : Option (Fin 4)) (n : Fin 1024) : Bool :=
  (List.finRange 5).all (fun k =>
    cosetCheck i n ((testAction k)⁻¹ * Pair00Two.normalTable n * testAction k))

def acceptedCheck (i : Option (Fin 4)) (n : Fin 1024) (j : Option (Fin 4)) : Bool :=
  memberCheck j (Pair00Two.normalTable n) &&
    (rowGenerators i).all (fun w => memberCheck j (wordAction w)) &&
    (rowGenerators j).all (fun w => cosetCheck i n (wordAction w))

def branchCheck (i : Option (Fin 4)) (n : Fin 1024) : Bool :=
  !squareCheck n || !commuteCheck i n || !conjugateCheck i n ||
    acceptedCheck i n (target i n)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue.InnerExtensions
