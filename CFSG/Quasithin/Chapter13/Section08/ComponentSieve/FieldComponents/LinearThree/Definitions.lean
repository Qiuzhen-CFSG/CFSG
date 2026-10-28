module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.Representation.PSL3Two.SmallModules
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Source actions and the five H.6.5 alternatives

`SourceAction` ties the binary representation to conjugation on the literal
source module U_H/V₁, acted on by H/O₂(H). The five H.6.5 alternatives use
actual intertwining linear equivalences with the concrete natural, seven-point
core, and trace-zero adjoint representations, including both direct sums.

These are shared interfaces for the conditional deductions in Aschbacher–Smith
13.8.19 and 13.8.21(1), printed pp.953 and 956–957. They assert neither the
classification of the source action nor the containment L₁ ≤ K.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree
variable {G : Type*} [Group G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- Conjugation restricted to the actual source conjugate span. -/
def conjugateUH (h : H) (u : Source.UH H V₃) : Source.UH H V₃ :=
  ⟨h.val * u.val * h.val⁻¹,
    le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H) h.val h.property
      u.val u.property⟩

/-- The action on U_H/V₁ induced by conjugation in H. Normality of V₁ is
only required inside U_H; both source containments are retained. -/
structure SourceAction where
  line_le : V₁ ≤ Source.UH H V₃
  seed_le : V₃ ≤ H
  representation : Representation (ZMod 2) (Source.Hstar H)
    (Additive (Source.Utilde H V₃ V₁))
  conjugation : ∀ (h : H) (u : Source.UH H V₃),
    representation (QuotientGroup.mk' (pCore 2 H) h)
      (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) =
    Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
      (conjugateUH H V₃ h u))
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree
open BinaryLinearThree
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) Group U)

/-- The literal five alternatives supplied by H.6.5. -/
def H65Alternatives : Prop :=
  Nonempty (ρ.Equiv W) ∨ Nonempty (ρ.Equiv U₂) ∨ Nonempty (ρ.Equiv S) ∨
    Nonempty (ρ.Equiv (W.prod S)) ∨ Nonempty (ρ.Equiv (U₂.prod S))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree
