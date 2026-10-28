module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.Reduction
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData

/-!
# The Held branch of the involution-fixed A₆ exclusion

In the inner `(E₄.L₃(4)).2` and outer `3A₇.2` rows, every component is the
normal quasisimple subgroup of index two. Its center has order four or
three, whereas A₆ is centerless. In the remaining `2^(1+6).L₃(2)` row,
the order 21504 is not divisible by 360.

The theorem below performs this component argument and assembles the inner
and outer cases using surjectivity from the full permutation normalizer.
The model rows and surjectivity remain explicit unproved inputs; this is
not yet the unconditional theorem `held`. In particular it does not claim
that the outer fixed subgroup has no components.

Sources: GLS3, Table 5.3p; Aschbacher–Smith, Theorem C, printed p.33,
and E.6.23, printed p.254 (PDF p.265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic

/-- Conditional assembly from the actual model calculations. Realization
and both local rows must be discharged before the Held branch is complete. -/
theorem held_of_involution_rows
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hinner : Held.InvolutionFixedData.InnerRows)
    (houter : Held.InvolutionFixedData.OuterRow) : FixedSixExclusion Held.He := by
  intro a ha K hK he
  have hcenter : center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  by_cases hi : ∃ g : Held.He, MulAut.conj g = a
  · obtain ⟨g, rfl⟩ := hi
    rcases hinner g ha with hcover | hcard
    · exact hcover.not_component_equiv (by decide) hcenter hK he
    · obtain ⟨e⟩ := he
      have hd := K.card_subgroup_dvd_card
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, hcard] at hd
      norm_num at hd
  · obtain ⟨n, rfl⟩ := hreal a
    exact (houter n ha hi).not_component_equiv (by decide) hcenter hK he

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic
