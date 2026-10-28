module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Alternatives
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction
public import Theory.SpecificGroups.BinaryComponentResidual.AlternatingSeven

/-!
# Constrained component reduction with explicit source obligations

The genuine A₆ and G₂(2)-block models identify the two-core quotient with
A₆ and G₂(2)′ respectively. Their checked rank and outer-automorphism facts
therefore apply to the original component. The source centralizer identity
then contradicts the exchanged fixed plane, for planes of order either four
or sixteen.

The final case deduction below is conditional on the source catalogue and
the three remaining block exclusions. It is not an unconditional proof of
15.1.26: the catalogue, rank-one exclusion, L₃(2)-block exclusion, and ordinary
A₇-block exclusion must still be proved from the original ambient hypotheses.
No `Facts` assertion for an unidentified quotient is assumed.

Source: Aschbacher--Smith 15.1.20--26, printed pp.1094--1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Original 15.1.25(1),(3) in the A₇-block branch, deriving the quotient
facts from its genuine natural-module model. This is not yet the A₇-block
contradiction in 15.1.25(5). -/
theorem ExchangedSource.constrained_a7_residual_and_movement
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hb : IsAlternatingBlock d.L 7) :
    d.L = (primeToResidual 3 d.G1).map d.G1.subtype ∧
      d.nineCubic = (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype ∧
      ¬ d.nineFixedPlane ≤ centralizer (d.L : Set G) := by
  obtain ⟨e⟩ := hb.2.2.quotient_iso
  have hf := Facts.of_equiv e alternatingSeven
  let := s.quasisimple
  obtain ⟨hL, hY⟩ := d.source_cubic_component hG h hf
  exact ⟨hL, hY, s.fixed_noncentral hf⟩

/-- The A₆ natural block supplies the actual quotient facts, so its
15.1.22 centralizer identity is impossible in either exchanged row. -/
theorem ExchangedSource.no_constrained_a6_centralizers
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V)
    (hb : IsAlternatingBlock d.L 6) : ¬ d.ConstrainedCentralizerIdentity := by
  obtain ⟨e⟩ := hb.2.2.quotient_iso
  exact s.no_equal_centralizers hG hTM h (Facts.of_equiv e alternatingSix)

/-- The G₂ block quotient is the derived binary group. The full G₂(2)
group is not substituted for it in the residual argument. -/
theorem ExchangedSource.no_constrained_g2_centralizers
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V)
    (hb : ChapterC.IsG2TwoBlock d.L) : ¬ d.ConstrainedCentralizerIdentity := by
  obtain ⟨e⟩ := hb.quotient_iso
  exact s.no_equal_centralizers hG hTM h (Facts.of_equiv e g2)

/-- Conditional final case deduction. Each extra source premise has a
separate mathematical obligation; none is asserted by this theorem. -/
theorem ExchangedSource.constrained_linear_quotient_of_source_alternatives
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V)
    (hc : d.ConstrainedAlternatives)
    (hrank : ¬ d.ConstrainedRankOneAlternative)
    (hthree : ¬ d.ConstrainedL3Alternative)
    (hseven : ¬ d.ConstrainedA7Alternative) :
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  cases hc with
  | rankOne source => exact (hrank source).elim
  | linearThree source => exact (hthree source).elim
  | alternatingSeven source => exact (hseven source).elim
  | alternatingSix block centralizers =>
    exact (s.no_constrained_a6_centralizers hG hTM h block centralizers).elim
  | g2 block centralizers =>
    exact (s.no_constrained_g2_centralizers hG hTM h block centralizers).elim
  | linear n degree equiv _ _ _ => exact ⟨n, degree, ⟨equiv⟩⟩

/-- Attach the fitting premise only after the actual quotient recognition.
The source catalogue and block exclusions remain explicit here. -/
theorem ExchangedSource.hasExchangedLinearSource_of_source_alternatives
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V)
    (hfit : generalizedFitting d.L = pCore 2 d.L)
    (hc : d.ConstrainedAlternatives)
    (hrank : ¬ d.ConstrainedRankOneAlternative)
    (hthree : ¬ d.ConstrainedL3Alternative)
    (hseven : ¬ d.ConstrainedA7Alternative) : d.HasExchangedLinearSource :=
  ⟨s, hfit, s.constrained_linear_quotient_of_source_alternatives hG hTM h hc hrank hthree hseven⟩

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
