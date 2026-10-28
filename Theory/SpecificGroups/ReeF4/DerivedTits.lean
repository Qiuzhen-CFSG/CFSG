module

public import Theory.SpecificGroups.ReeF4.DerivedTits.Reduction
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization
public import Theory.SpecificGroups.ReeF4.DerivedTits.BruhatBound

/-!
# Comparing the derived binary Ree group with Parrott's Tits group

The exceptional fixed root/Weyl matrices satisfy all 37 Parrott relations and
give a nontrivial image of the certified simple Tits presentation. This image
is faithful and perfect. The restricted Bruhat count bounds the full binary
Ree group by 35942400, so the image has index at most two. Perfectness puts the
image inside the ambient commutator subgroup, while the index bound gives the
reverse inclusion. Thus the derived subgroup of `Model 0` is isomorphic to
`Tits.ParrottGroup`.

The unconditional comparison below supplies both concrete inputs to the
retained assembly interface. The full `Model 0` remains the exceptional
fixed-point group ²F₄(2); the comparison concerns its derived subgroup.

Sources: Parrott (1972), §5, printed p.683; GLS3, Theorem 2.2.7(a) and §§2.3--2.4;
Aschbacher--Smith,
F.1.12 and its binary discussion, printed pp.263--264 of `refs/quasithin.pdf`.
-/

namespace ReeF4.DerivedTits

/-- Final assembly interface for the independent matrix-realization and
fixed-point size calculations. -/
public theorem nonempty_derived_equiv_of_realization_and_card_lt
    (hreal : ∃ g : Tits.ParrottGenerator → SplitGroup 0,
      (∀ i, reeTwist 0 (g i) = g i) ∧
      Tits.SatisfiesParrottRelations g ∧ (∃ i, g i ≠ 1))
    (hcard : Nat.card (Model 0) < 3 * 17971200) :
    Nonempty (commutator (Model 0) ≃* Tits.ParrottGroup) := by
  obtain ⟨g, hfix, hrel, hne⟩ := hreal
  exact nonempty_derived_equiv_of_split_assignment g hfix hrel hne hcard

/-- The derived subgroup of the full binary Ree matrix group is isomorphic to
Parrott's certified Tits group. The fixed matrix realization and the ambient
size bound are both discharged, with no recognition or generation premise. -/
public theorem nonempty_derived_equiv :
    Nonempty (commutator (Model 0) ≃* Tits.ParrottGroup) :=
  nonempty_derived_equiv_of_realization_and_card_lt parrott_realization binary_card_lt

end ReeF4.DerivedTits
