module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words00
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words01
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words02
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words03
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words04
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words05
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words06
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words07
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words08
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words09
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words10
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words11
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words12
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words13
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words14
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words15
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words16
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words17
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Representatives.Words18

/-!
# Candidate double-coset words for the marked Held subgroup

These 4,831 words are actual elements of the existing Held carrier.
GAP found one per double coset of the marked subgroup. Exhaustiveness
is a separate theorem to be proved; it does not follow from these definitions.
The adjacent JSON also retains candidate local expressions and prime-order
obstruction words. Those require independent kernel checks.

Source: the ATLAS degree-2058 generators and local subgroup programs;
`source/generate_representatives.py` preserves the existing word convention.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.SylowOvergroups

def representativeWord (i : Fin 4831) : List (Bool × ℤ) :=
  match i.val / 256 with
  | 0 => wordBlock00[i.val % 256]!
  | 1 => wordBlock01[i.val % 256]!
  | 2 => wordBlock02[i.val % 256]!
  | 3 => wordBlock03[i.val % 256]!
  | 4 => wordBlock04[i.val % 256]!
  | 5 => wordBlock05[i.val % 256]!
  | 6 => wordBlock06[i.val % 256]!
  | 7 => wordBlock07[i.val % 256]!
  | 8 => wordBlock08[i.val % 256]!
  | 9 => wordBlock09[i.val % 256]!
  | 10 => wordBlock10[i.val % 256]!
  | 11 => wordBlock11[i.val % 256]!
  | 12 => wordBlock12[i.val % 256]!
  | 13 => wordBlock13[i.val % 256]!
  | 14 => wordBlock14[i.val % 256]!
  | 15 => wordBlock15[i.val % 256]!
  | 16 => wordBlock16[i.val % 256]!
  | 17 => wordBlock17[i.val % 256]!
  | 18 => wordBlock18[i.val % 256]!
  | _ => []

/-- Evaluation in Held proves membership, without a recognition assumption. -/
def representative (i : Fin 4831) : He :=
  wordEval a b (representativeWord i)

end Held.LocalPairs.PairCoverage.SylowOvergroups
