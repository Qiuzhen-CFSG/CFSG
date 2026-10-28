module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved.Irreducible
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleInvariance
public import Theory.Representation.BinaryOffender.Replacement

/-!
# Discharging the irreducible-invariance input

Thompson replacement makes every minimal best offender quadratic. Applying
the proved B.7.2(1) to each of its elements therefore gives the full B.1.5(3)
implication used by the external L₂ no-strong reduction. All residual and
relative chief-factor hypotheses are retained. The conclusion stabilizes
each Irr⁺ subspace; it does not fix its vectors pointwise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.4(3),
B.1.5(3), printed pp.68–70, and B.7.2(1–2), printed p.119.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo

universe u v

/-- The complete universal invariance input, proved from replacement and
B.7.2(1), with no specialized stabilization premise remaining. -/
theorem fullIrrInvariance : NoStrongMoved.FullIrrInvariance.{u,v} := by
  intro D _ _ V _ _ _ ρ hf A X hA hn hr hc hchief I hI a ha
  exact CFSG.Quasithin.ChapterB.source_lemma_B_7_2_1 ρ hf hA.1 hn hr hc hchief
    ha (fun b hb v => hA.isQuadratic ρ b hb a ha v) hI

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo

end
