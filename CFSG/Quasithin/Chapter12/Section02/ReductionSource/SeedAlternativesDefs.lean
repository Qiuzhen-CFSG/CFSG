module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.Models

/-!
# The literal chosen-seed alternatives

Keep the seed V, its T-orbit and its N_G(L)-orbit distinct. The moved
alternative retains the same conjugator, both orbit equalities, trivial
intersection, nonisomorphism for the unchanged L-action, and genuine
constituent coordinates. No alternative is asserted by these definitions.

Source: Aschbacher--Smith 3.2.5, with the separate A7 clause of D.3.10,
printed pp.580 and201, as used in12.2.2, pp.794--795.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The marked moved-seed alternative of source 3.2.5, retaining the A₇
four-space alternative as explicitly stated in D.3.10. Both orbit equalities,
the actual conjugator, disjointness and module nonisomorphism are retained. -/
def MarkedDoubled (D : ChosenModule T L V) : Prop :=
  V ⊓ centralizer (L : Set G) = ⊥ ∧
  ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype) ∧
  ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
    componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G) ∧
    componentOrbit V (T : Subgroup G) = V ⊔ V.map (MulAut.conj t).toMonoidHom ∧
    V ⊓ V.map (MulAut.conj t).toMonoidHom = ⊥ ∧
    ¬ SameConjugationModule L V (V.map (MulAut.conj t).toMonoidHom)

/-- The qualitative source alternatives on the literal chosen seed. This is
only a statement of the conclusion, not an assertion that it always holds. -/
def Source325Alternatives (D : ChosenModule T L V) : Prop :=
  (componentOrbit V (T : Subgroup G) = V ∧
    componentOrbit V (normalizer (L : Set G)) = V) ∨
  (componentOrbit V (T : Subgroup G) = V ∧ V ⊓ centralizer (L : Set G) = ⊥ ∧
    ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V) ∨ D.MarkedDoubled

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
