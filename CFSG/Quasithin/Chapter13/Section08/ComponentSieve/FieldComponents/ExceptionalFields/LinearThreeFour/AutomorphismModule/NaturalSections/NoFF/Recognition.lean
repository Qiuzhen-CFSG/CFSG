module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NoFF.Recognition.Transport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NoFF.Recognition.Coordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NoFF.Recognition.Sieve

/-!
# Specializing the full B.5.1 conclusion to SL₃(4)

The complete B.4.2 model sieve leaves only the degree-three natural module
in B.5.1(1i); the field is identified with the concrete four-element field.
Case (1ii) supplies two copies with the same marking, whose fixed space is
zero. The higher-rank binary cases are excluded by their centers. This gives
one or two natural copies on the literal moved central quotient.

For K ≤ J ≤ D with K normal in D, the moved and fixed subspaces over J
are the same subspaces over D. Normality extends their actions to D; only
the section, not any individual summand, is asserted to be D-invariant.
The resulting marking may differ from the initially supplied K ≃ SL₃(4).

This proves a conditional specialization of the FULL existing B.5.1
conclusion. It does not prove B.5.1 or assume a graph actor, semisimplicity,
homogeneity, or the no-FF conclusion. The parent no-FF assembly must still
supply B.5.1 and its hypotheses.

Source: Aschbacher–Smith, B.5.1, printed pp.99–103, referring to B.4.2,
p.86, applied in F.9.18(7) and 13.8.20, p.955, combined manuscript of
1 March 2004.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.SL3FourNaturalDual
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF.Recognition
universe u v
variable {D : Type u} [Group D] [Finite D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- Over the B.5.1 ambient group, the literal moved central section has one or two natural copies. -/
theorem repeatedSection_of_source {K : Subgroup D} (eK : K ≃* SL)
    (h : QuasisimpleSourceConclusion ρ K) :
    ∃ s : RepeatedNaturalSection ρ K, s.copies = 1 ∨ s.copies = 2 := by
  cases h.clause_one with
  | irreducible _ _ _ hcase _ =>
    obtain ⟨E, hE, ⟨e⟩⟩ := irreducible_linearThree h.sectionData.action eK hcase
    exact ⟨quotientRepeatedSection h.sectionData 1 (by decide) (concreteSingleEquiv E hE e),
      Or.inl rfl⟩
  | doubleThree E _ e _ _ =>
    have hE := linearThree_card E (eK.symm.trans e.groupEquiv)
    exact ⟨spaceRepeatedSection h.sectionData 2 (by decide) (concreteRepeatedEquiv E hE 2 e),
      Or.inr rfl⟩
  | naturalDual d hd _ he =>
    obtain ⟨e⟩ := he
    exact (not_binaryLinear d hd (eK.symm.trans e.groupEquiv)).elim
  | repeatedNatural d r hd _ _ _ he =>
    obtain ⟨e⟩ := he
    exact (not_binaryLinear d hd (eK.symm.trans e.groupEquiv)).elim

/-- The full B.5.1 conclusion over J supplies natural coordinates on the actual
D-invariant moved central section, with multiplicity one or two. -/
theorem repeatedNaturalSection_of_quasisimpleSourceConclusion
    {K J : Subgroup D} [K.Normal] (hKJ : K ≤ J) (eK : K ≃* SL)
    (h : QuasisimpleSourceConclusion (ρ.comp J.subtype) (K.subgroupOf J)) :
    ∃ s : RepeatedNaturalSection ρ K, s.copies = 1 ∨ s.copies = 2 := by
  obtain ⟨s, hs⟩ := repeatedSection_of_source (ρ.comp J.subtype)
    ((subgroupOfEquivOfLe hKJ).trans eK) h
  exact ⟨ambientRepeatedNaturalSection ρ hKJ s, hs⟩

/-- The repeated-natural witness consumed by the no-FF assembly. The B.5.1
classification conclusion is the only classification premise. -/
theorem nonempty_repeatedNaturalSection_of_quasisimpleSourceConclusion
    {K J : Subgroup D} [K.Normal] (hKJ : K ≤ J) (eK : K ≃* SL)
    (h : QuasisimpleSourceConclusion (ρ.comp J.subtype) (K.subgroupOf J)) :
    Nonempty (RepeatedNaturalSection ρ K) := by
  obtain ⟨s, _⟩ := repeatedNaturalSection_of_quasisimpleSourceConclusion ρ hKJ eK h
  exact ⟨s⟩


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF.Recognition
