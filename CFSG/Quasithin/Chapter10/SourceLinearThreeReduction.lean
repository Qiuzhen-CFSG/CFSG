module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Numerical

/-!
# Assembly of the original non-A5 survivor from independent source inputs

Perfectness gives an eight-element lower bound for the moved factor, so
point-centralizer control gives r≥3. The actual H* generation bound then
forces w≤2. Small-offender recognition supplies the natural SL₃(2) section
and the reverse inequality on a reselected seed with the same full module.
Thus w=2, and the comparison with every actual H* forces n(H)=2 there.
The exchanged-factor generation is constructed from the original orbit
theorem, with the same exchanger used in crossed centralization.

The three earlier source inputs remain explicit. This is a conditional
assembly of 10.2.13, not an unconditional proof of it or of 10.0.1.
The separate `SourceLinearThreeReduction.Normalization` module applies this
reduction to normalization without creating a backwards import dependency.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Corollary 10.2.13 and §10.3, printed pp.755--757.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The exact published survivor contract, retaining all three genuinely
independent earlier source obligations. No parameter equality is assumed. -/
theorem source_nonnormalReduction_of_point_generation_smallOffender
    (hpoint : SourceNonnormalPointControlAt T)
    (hgeneration : SourceNonnormalGenerationBoundAt T)
    (hsmall : SourceNonnormalSmallOffenderAt T) : SourceNonnormalReductionAt T := by
  intro hmany L hL hf hq hn hnotA5
  obtain ⟨D,hD,hcent⟩ := hpoint hmany L hL hf hq hn hnotA5
  have hb := hgeneration hmany L D hn hnotA5
  have hw := source_fullModule_globalW_le_two_of_generation_bound D hmany hcent hb
  obtain ⟨g,hg,hcomm,hwg,hcorank⟩ := source_fullModule_small_offender D hw
  obtain ⟨E,hED,⟨m⟩,hwl⟩ := hsmall hmany L D hD hn hnotA5 hcent g hg hcomm hwg hcorank
  have hcentE : ∀ v ∈ ⁅E.fullModule,L⁆, v ≠ 1 →
      centralizer ({v} : Set G) ≤ E.maximalLocal := by
    simpa only [hED] using hcent
  have hbE : ∀ H ∈ Chapter3.HStar (T : Subgroup G) E.maximalLocal,
      generationParameter H ≤ 2 := hb
  obtain ⟨hwe,hne⟩ := source_fullModule_parameters_eq_two_of_lower_bound
    E hmany hcentE hbE hwl
  obtain ⟨t,ht,htn,_,hpair,_⟩ := source_nonnormal_fullModule_pair E hn
  exact ⟨E,⟨{
    exchange := t
    exchange_mem := ht
    exchange_moves := htn
    full_eq_local := m.full_eq_local
    generated := hpair
    crossed := m.crossed t ht htn
    quotient := m.quotient
    natural := m.natural
    weakClosure := hwe
    generation := hne
    pointCentralizers := hcentE }⟩⟩

end CFSG.Quasithin.Chapter10
