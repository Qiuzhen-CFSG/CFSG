module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Inputs

/-!
# Remaining model-generation branches

The prime-five conversion and invariant L₄(2), L₅(2) rows are proved
separately. These two propositions isolate the remaining odd-prime orbit
and invariant Held calculations. They are unproved obligations, not source
assertions. Each uses the genuine C-component, its literal two-core and a
full Sylow supplement. The final assembly supplies every local input from
the original maximal two-local overgroup.

Source: Aschbacher--Smith 10.3.3 and its final reuse, pp.756--757, with
E.1.11--14, pp.212--214. Held is retained from the corrected intrinsic 1.3.4.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
universe u

/-- Generation for the entire prime-model component orbit, including the
case where the full Sylow subgroup moves the component. -/
def OddPrimeOrbitGeneration : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsSQTK KnownSimple.IsKnownSimple H →
    ∀ (S : Sylow 2 H) (K : Subgroup H), K.IsCComponent →
      IsQuasisimple (K ⧸ pCore 2 K) → K ⊔ (S : Subgroup H) = ⊤ →
      ∀ p : ℕ, p.Prime → Odd p → 7 ≤ p →
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p → ChapterE.IsEGenerated 1 H

/-- The Held branch retains relative normality and the actual Held carrier.
The known conditional local-pair theorem alone does not establish this. -/
def InvariantHeldGeneration : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsSQTK KnownSimple.IsKnownSimple H →
    ∀ (S : Sylow 2 H) (K : Subgroup H), K.IsCComponent → K.Normal →
      IsQuasisimple (K ⧸ pCore 2 K) → K ⊔ (S : Subgroup H) = ⊤ →
      Nonempty ((K ⧸ pCore 2 K) ≃* Held.He) → ChapterE.IsEGenerated 1 H

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
