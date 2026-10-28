module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action

/-!
# The constituent alternative in 15.3.57(2)

This interface records the two actual subspaces, their internal direct sum,
their irreducible restricted actions, equal dimensions, and rank-one action
of the marked involution on each. It is a conclusion to be proved, not an
assumption that establishes the source lemma by itself.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1148.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

/-- The precise two-summand conclusion: both invariant summands carry a
transvection, expressed by the rank of their literal displacement map. -/
def TwoSummandAlternative (ρ : Representation (ZMod 2) H W)
    (K : Subgroup H) (v : H) (s : ℕ) : Prop :=
  ∃ J₁ J₂ : Subrepresentation (ρ.comp K.subtype),
    IsCompl J₁.toSubmodule J₂.toSubmodule ∧
    J₁.toRepresentation.IsIrreducible ∧ J₂.toRepresentation.IsIrreducible ∧
    Module.finrank (ZMod 2) J₁.toSubmodule = s + 2 ∧
    Module.finrank (ZMod 2) J₂.toSubmodule = s + 2 ∧
    J₁.toSubmodule.map (ρ v) = J₁.toSubmodule ∧
    J₂.toSubmodule.map (ρ v) = J₂.toSubmodule ∧
    Module.finrank (ZMod 2)
      (LinearMap.range ((ρ v - LinearMap.id).comp J₁.toSubmodule.subtype)) = 1 ∧
    Module.finrank (ZMod 2)
      (LinearMap.range ((ρ v - LinearMap.id).comp J₂.toSubmodule.subtype)) = 1

/-- The full conclusion requested by 15.3.57(2), on a specified action. -/
def NormalConstituentConclusion (ρ : Representation (ZMod 2) H W)
    (K : Subgroup H) (v : H) (s : ℕ) : Prop :=
  ⁅K, Subgroup.zpowers v⁆ ≠ ⊥ ∧
    (Representation.IsIrreducible (ρ.comp K.subtype) ∨ TwoSummandAlternative ρ K v s)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
