module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Normal

/-!
# Reduction of the odd-prime obligation to moved components

The normal component case is proved by the exact simple quotient and its
Sylow supplement. Only a component moved by that Sylow subgroup remains.
The predicate below is an outstanding model obligation, with no hidden
generation premise or conclusion supplied as a record field.

Source: Aschbacher--Smith 10.3.3, pp.756--757, with E.1.11--14 and E.2.2.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
universe u

/-- The remaining odd-prime calculation, preserving the full Sylow and
the literal component quotient. Normal components are already discharged. -/
def MovedOddPrimeGeneration : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsSQTK KnownSimple.IsKnownSimple H →
    ∀ (S : Sylow 2 H) (K : Subgroup H), K.IsCComponent → ¬K.Normal →
      IsQuasisimple (K ⧸ pCore 2 K) → K ⊔ (S : Subgroup H) = ⊤ →
      ∀ p : ℕ, p.Prime → Odd p → 7 ≤ p →
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p → ChapterE.IsEGenerated 1 H

/-- The completed normal-row proof removes that branch from the remaining
input to the exact original model-generation assembly. -/
theorem oddPrimeOrbitGeneration_of_moved (hmoved : MovedOddPrimeGeneration.{u}) :
    OddPrimeOrbitGeneration.{u} := by
  intro H _ _ hH S K hK hq hgen p hp ho hlarge hm
  by_cases hn : K.Normal
  · let := hn
    let := hq
    exact isEGenerated_of_normal_odd_component hH S K hK hgen ho hlarge hm
  · exact hmoved H hH S K hK hn hq hgen p hp ho hlarge hm

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
