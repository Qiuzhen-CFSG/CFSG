module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Definitions
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# The marked inputs to the Rudvalis two-primary calculation

The first ATLAS max4 generator is fixed as an element of the literal max4
subgroup. The two propositions below separate a calculation of local covers
from ambient involution fusion. They are explicit proof obligations, not
assertions of those calculations or of the Rudvalis multiplier theorem.

The local calculation must show that perfect two-kernel covers of max4 have
kernel of exponent two, and that an involutory lift of the marked generator
reduces their kernel order to at most two. The ambient calculation constructs
that lift when the kernel has exponent two. Their consumer is `Reduction`.
Source: Aschbacher--Smith I.1.3(1), printed p.407; the actual max4 words and
ATLAS attribution are in `SylowOvergroups.Definitions`.
-/

namespace Rudvalis.Multiplier.TwoPrimary
open SylowOvergroups PerfectCentralCovering

/-- The first original ATLAS max4 generator, with its subgroup membership. -/
@[expose] public def max4First : max4 :=
  ⟨max4Generators.1, Subgroup.subset_closure (by simp)⟩

/-- The local central-extension calculation required by the upper-bound route.
No witness of this proposition is supplied in this module. -/
@[expose] public def Max4CoverBounds : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (c : Cover D max4),
    IsPGroup 2 c.toMonoidHom.ker →
      (∀ z ∈ c.toMonoidHom.ker, z ^ 2 = 1) ∧
      ((∃ x : D, c.toMonoidHom x = max4First ∧ x ^ 2 = 1) →
        Nat.card c.toMonoidHom.ker ≤ 2)

/-- The independent ambient fusion calculation, with the elementary-kernel
premise left explicit. No witness is supplied in this module. -/
@[expose] public def FirstInvolutionLift : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (c : Cover E Model),
    (∀ z ∈ c.toMonoidHom.ker, z ^ 2 = 1) →
      ∃ x : E, c.toMonoidHom x = max4Generators.1 ∧ x ^ 2 = 1

end Rudvalis.Multiplier.TwoPrimary
