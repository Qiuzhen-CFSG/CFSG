module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.Selection
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.LocalRadical
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.AlternatingFive.BlockTransport
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.SourceEndgame

/-!
# The exchanged-component source sieve

Apply the complete universal C.2.7 theorem to the selected component. Its
actual local radical is proved from the original source geometry, so the
complete universal C.1.34 theorem excludes the SL₃ branch without an extra
radical or binary-model premise. All remaining quotient comparisons leave
only the natural rank-one block and the alternating-five block. The latter
contradicts the original module and Sylow seed.

The endgame object retains the very same component, exchanger, product and
natural-module model. Only the complete earlier-source implications and the
genuine C.2.7 component hypotheses remain explicit; their existing producers
are qt-c-02-offender-cases, qt-c01-rank-two, and
qt-15-04-sylow-core-component-inputs.
Source: Aschbacher--Smith, 15.4.20, printed p.1164, and C.2.7 and C.1.34.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

/-- The same selected component survives the complete C.2.7 sieve, with no
extra local-radical or component-model input. -/
theorem selectedConclusion
    (c27 : UniversalC27.{u})
    (c134 : SL3Geometry.SourceCases.UniversalClassification.{u})
    (h : Input d i j H U K) (s : Selected H U K K₁ r) (κ : GroupClass.{u})
    (hc : ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H)) :
    SelectedConclusion H U K K₁ r :=
  selectedConclusion_of_local_radical c27 c134 h s κ hc
    (source_local_radical h s hc.normalized)

/-- The actual alternating-five module is incompatible with the source's
internal module and Sylow seed, leaving the original rank-one block. -/
theorem selected_rankOne
    (c27 : UniversalC27.{u})
    (c134 : SL3Geometry.SourceCases.UniversalClassification.{u})
    (h : Input d i j H U K) (s : Selected H U K K₁ r) (κ : GroupClass.{u})
    (hc : ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H)) :
    ∃ n, Even n ∧ Nat.ModEq 3 (2 ^ n) 1 ∧ ChapterC.IsL2EvenBlock K₁ n := by
  rcases (selectedConclusion c27 c134 h s κ hc).2.2 with hb | hb
  · exact hb
  · exact (h.not_alternatingFive_block K₁ s.component.1 s.relative_subnormal hb).elim

/-- The existential sieve target retains the chosen component and exchanger. -/
theorem exchangedL2Block
    (c27 : UniversalC27.{u})
    (c134 : SL3Geometry.SourceCases.UniversalClassification.{u})
    (h : Input d i j H U K) (s : Selected H U K K₁ r) (κ : GroupClass.{u})
    (hc : ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H)) : ExchangedL2Block H U K := by
  obtain ⟨n, he, hm, hb⟩ := selected_rankOne c27 c134 h s κ hc
  exact ⟨K₁, r, n, s.component, s.relative_subnormal, s.conjugator_mem,
    s.conjugator_moves, s.join_eq, s.product_eq, he, hm, hb⟩

/-- Construct the endgame's literal block object, with the selected first
component and its given ambient conjugator. -/
noncomputable def exchangedBlock
    (c27 : UniversalC27.{u})
    (c134 : SL3Geometry.SourceCases.UniversalClassification.{u})
    {κ : GroupClass.{u}} (c : BlockEndgame.ContraryData κ d i j)
    (h : Input d i j c.H c.U c.K) (s : Selected c.H c.U c.K K₁ r)
    (hc : ComponentHypotheses κ c.H ((sourceRadical d c.U).subgroupOf c.H)
      (d.M₁.subgroupOf c.H) (K₁.subgroupOf c.H)) : BlockEndgame.ExchangedBlock c := by
  classical
  let hb := selected_rankOne c27 c134 h s κ hc
  let n := Classical.choose hb
  have hn := Classical.choose_spec hb
  refine {
    first := K₁
    first_le := s.component.1
    relative_block := ⟨inferInstance, ?_, s.relative_subnormal⟩
    quotient_quasisimple := ?_
    n := n
    even_parameter := hn.1
    model := hn.2.2
    exchanger := r
    exchanger_mem := s.conjugator_mem
    exchanger_moves := s.conjugator_moves
    product := s.join_eq
    product_set := s.product_eq.symm
    core_normalizes := ?_ }
  · exact ChapterC.RankOne.Solvable.isShort_of_equiv
      (subgroupOfEquivOfLe s.component.1).symm hn.2.2.2.1
  · let := hc.quasisimple
    exact IsQuasisimple.of_mulEquiv s.internalQuotientEquiv.symm
  · have hRH : sourceRadical d c.U ≤ c.H :=
      h.radical_le_sylow.trans (h.placed.sylow_image ▸ map_subtype_le _)
    have he := hc.normalized
    rw [← subgroupOf_normalizer_eq s.component.1] at he
    exact fun x hx => he (show (⟨x, hRH hx⟩ : c.H) ∈
      (sourceRadical d c.U).subgroupOf c.H from hx)

@[simp] theorem exchangedBlock_first
    (c27 : UniversalC27.{u})
    (c134 : SL3Geometry.SourceCases.UniversalClassification.{u})
    {κ : GroupClass.{u}} (c : BlockEndgame.ContraryData κ d i j)
    (h : Input d i j c.H c.U c.K) (s : Selected c.H c.U c.K K₁ r)
    (hc : ComponentHypotheses κ c.H ((sourceRadical d c.U).subgroupOf c.H)
      (d.M₁.subgroupOf c.H) (K₁.subgroupOf c.H)) :
    (exchangedBlock c27 c134 c h s hc).first = K₁ := rfl

@[simp] theorem exchangedBlock_exchanger
    (c27 : UniversalC27.{u})
    (c134 : SL3Geometry.SourceCases.UniversalClassification.{u})
    {κ : GroupClass.{u}} (c : BlockEndgame.ContraryData κ d i j)
    (h : Input d i j c.H c.U c.K) (s : Selected c.H c.U c.K K₁ r)
    (hc : ComponentHypotheses κ c.H ((sourceRadical d c.U).subgroupOf c.H)
      (d.M₁.subgroupOf c.H) (K₁.subgroupOf c.H)) :
    (exchangedBlock c27 c134 c h s hc).exchanger = r := rfl

/-- The actual endgame consumer: after the source sieve constructs the same
exchanged block, the established field-four/seed argument closes the contrary
configuration. -/
theorem sieve_contradiction
    (c27 : UniversalC27.{u})
    (c134 : SL3Geometry.SourceCases.UniversalClassification.{u})
    {κ : GroupClass.{u}} (c : BlockEndgame.ContraryData κ d i j)
    (h : Input d i j c.H c.U c.K) (s : Selected c.H c.U c.K K₁ r)
    (hc : ComponentHypotheses κ c.H ((sourceRadical d c.U).subgroupOf c.H)
      (d.M₁.subgroupOf c.H) (K₁.subgroupOf c.H)) : False :=
  BlockEndgame.source_contradiction c (exchangedBlock c27 c134 c h s hc)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
