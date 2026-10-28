module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Mathlib.GroupTheory.Frattini

/-!
# The intermediate five-primary configuration in 13.8.13

This is a contract between the supercritical/three-primary reduction and
the five-primary action calculation. It uses actual subgroup images in
H/O₂(H). Irreducibility on P*/Φ(P*) is expressed by its invariant subgroup
interval, so it cannot refer to an unrelated linear action.

The contract does not assert existence. Its construction, including the
exclusion of the three-primary alternatives, remains an obligation. It
contains neither solvable-overgroup exclusion nor a contradiction witness.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed pp.950–951, through the paragraph beginning “We have reduced”.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
open Subgroup
variable {G : Type*} [Group G]

/-- The intrinsic Frattini subgroup of P*, embedded into H*. -/
def starFrattini (H P : Subgroup G) : Subgroup (Source.Hstar H) :=
  (frattini (Source.starImage H P)).map (Source.starImage H P).subtype

/-- Conjugation by L₁*T* is irreducible on the actual Frattini quotient.
Normality of P* is a separate hypothesis of `ReducedFive`, and nontriviality
of this finite p-group follows from the nontrivial commutator there. -/
def starFrattiniIrreducible (H P L₁ T : Subgroup G) : Prop :=
  ∀ N : Subgroup (Source.Hstar H), starFrattini H P ≤ N →
    N ≤ Source.starImage H P →
    Source.starImage H (L₁ ⊔ T) ≤ normalizer (N : Set (Source.Hstar H)) →
    N = starFrattini H P ∨ N = Source.starImage H P

/-- An intermediate configuration to be constructed from a hypothetical
minimal solvable member of Hz. The five-primary calculation takes this
configuration and the genuine standing local setup as separate inputs. -/
structure ReducedFive (H L₁ T M Vα : Subgroup G) where
  P : Subgroup G
  P_le : P ≤ H
  P_isPGroup : IsPGroup 5 P
  Pstar_normal : (Source.starImage H P).Normal
  moved : ⁅Source.starImage H P, Source.starImage H Vα⁆ ≠ ⊥
  outside : ¬ P ≤ M
  generated : H = P ⊔ (L₁ ⊔ T)
  irreducible : starFrattiniIrreducible H P L₁ T

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
end
