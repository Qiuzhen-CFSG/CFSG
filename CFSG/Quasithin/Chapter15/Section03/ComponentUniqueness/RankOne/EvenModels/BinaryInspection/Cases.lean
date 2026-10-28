module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.SourceReduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.SmallLinear
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The three remaining binary inspection branches

Specializing the genuine source model list to field degree one excludes the
larger fields and central covers. The existing PSL₃(2) calculation closes
that branch. The actual projective derived symplectic equivalence identifies
Sp₄(2)' with A₆; its inherited involution is inner. The separate source A₆
branch retains the transposition action and first excludes its triple cover.

Every remaining alternative contains an actual model equivalence and retains
the prescribed action. This is an exhaustive case reduction, not a local
classification: the linear, exceptional and six-letter inspections must still
be proved and assembled before the binary case of 15.3.43 is complete.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 1.1.5(3)(a),(c),
printed pp.501--502; A.2.3--4, p.33; and 15.3.43, p.1140.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection

/-- The three exceptional binary carriers left after the parameter reduction. -/
inductive ExceptionalModel (H : Type*) [Group H] : Prop
  | g2Derived (iso : Nonempty (H ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | triality (iso : Triality.Standard.IsTrialityGroupAt 2 H)
  | tits (iso : Nonempty (H ≃* Tits.ParrottGroup))

/-- Concrete remaining models, retaining the action of the source involution. -/
inductive RemainingModel {G : Type*} [Group G] (L : Subgroup G) (z : G) : Prop
  | linear (simple : IsSimpleGroup L) (d : ℕ) (dimension : d = 4 ∨ d = 5)
      (iso : ClassicalGroup.IsPSL L d 2) (inner : ActsInner L z)
  | exceptional (simple : IsSimpleGroup L) (model : ExceptionalModel L)
      (inner : ActsInner L z)
  | alternatingSix (iso : Nonempty (L ≃* alternatingGroup (Fin 6)))
      (action : ActsInner L z ∨ ActsTransposition L z)

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
include c

/-- Exhaust the source binary list without assuming any parabolic classification. -/
theorem remaining_model {z : G} (hm : Model L z 1) : RemainingModel L z := by
  cases hm with
  | simple hs hm hi =>
    cases hm with
    | linearTwo hn _ => omega
    | unitaryThree hn _ => omega
    | binaryLinear _ d hd iso => exact .linear hs d hd iso hi
    | rankTwo hm =>
      cases hm with
      | linear _ iso => exact (not_linear_three_binary c (by simpa using iso)).elim
      | symplectic hn _ => omega
      | g2 hn _ => omega
      | triality _ iso => exact .exceptional hs (.triality (by simpa using iso)) hi
      | ree_f4 m hm hn _ => omega
      | symplectic_derived _ iso =>
        obtain ⟨e⟩ := iso
        exact .alternatingSix ⟨e.trans
          Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩
          (Or.inl hi)
      | g2_derived _ iso => exact .exceptional hs (.g2Derived iso) hi
      | tits _ iso => exact .exceptional hs (.tits iso) hi
  | linearThreeCover hn _ _ _ => omega
  | g2Cover hn _ _ _ => omega
  | alternatingSix _ hc ha =>
    exact .alternatingSix (alternating_six_of_source_center c hc ha) (Or.inr ha)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection
