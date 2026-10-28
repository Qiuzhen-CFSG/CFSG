module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Factors
public import Theory.Representation.BinaryOffender.Stability
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable
public import Theory.PGroupCore

/-!
# The permitted universal input to the cyclic-three calculation

`SolvableFFStructure` records the valid conclusions of B.1.8 for one action.
`SolvableFFTheorem` is a universally quantified theorem contract, not an axiom
or an existence assertion. The owner of B.1.8 must supply a proof before an
unconditional B.1.12 can be assembled.

The factor witness includes actual group and equivariant module equivalences.
Best offenders are nonempty products of coordinate Sylow two-subgroups. A
stable family generates a product of selected whole factors; the false printed
assertion that the family equals its saturation is deliberately absent.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1.8, printed p. 70 (PDF p. 81).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ThreeConjugates
open Representation.BinaryOffender

/-- The valid B.1.8 data that the source-theorem owner must construct. -/
structure SolvableFFStructure {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) extends SolvableFFFactors ρ where
  ratio_one : quadraticRatio ρ = 1
  best_rank_eq : ∀ A, IsBestOffender ρ A → fixedCodim ρ A = rank A
  offender_product : ∀ A, IsBestOffender ρ A ↔ A ≠ ⊥ ∧
    ∃ B : Fin count → Subgroup G,
      (∀ i, B i = ⊥ ∨ ∃ S : Sylow 2 (factor i),
        (S : Subgroup (factor i)).map (factor i).subtype = B i) ∧ A = ⨆ i, B i
  stable_product : ∀ P, IsStable ρ P →
    ∃ I : Set (Fin count), generatedBy P ⊤ = ⨆ i ∈ I, factor i

/-- A callable universal B.1.8 hypothesis. It contains no assertion about K,
its conjugates, or the quotient in B.1.12. -/
def SolvableFFTheorem : Prop :=
  ∀ (G V : Type*) [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V),
    Group.IsSolvable G → pCore 2 G = ⊥ → Function.Injective ρ → IsFFModule ρ →
      Nonempty (SolvableFFStructure ρ)

end CFSG.Quasithin.ChapterB.ThreeConjugates
