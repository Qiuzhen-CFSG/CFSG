module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Inputs

/-!
# Transport and centralizer control for the original minimum offender

Minimal seed reselection preserves the full module and every hypothesis of
the literal offender configuration. Point-centralizer control gives r≥3,
while the supplied offender gives w≤2. Consequently its entire centralizer
lies in the conjugate maximal local subgroup. These statements prepare the
recognition and corank-one arguments without assuming a module model.

Source: Aschbacher--Smith, 10.2.9(2), 10.2.12 and E.3.3--5, printed
pp.750,754--755 and231--232; minimal reselection uses 3.2.3 on p.580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender
open Chapter3.Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {g : G}

/-- Minimality makes a contained reselected full module equal to the original
one, preserving the actual offender, all point centralizers and minimality. -/
theorem Configuration.reselect (c : Configuration T D g)
    (E : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hE : E.fullModule ≤ D.fullModule) :
    E.fullModule = D.fullModule ∧ Configuration T E g := by
  have he := c.minimal.eq_of_le E hE
  refine ⟨he, ⟨c.many, ?_, c.nonnormal, c.notA5, ?_, c.outside, ?_, ?_, ?_⟩⟩
  · intro F
    rw [he]
    exact c.minimal F
  · simpa only [he] using c.pointCentralizers
  · simpa only [he] using c.noncommuting
  · simpa only [he] using c.attained
  · simpa only [he] using c.small

/-- The published literal intersection is exactly E.3's offender normalizer. -/
theorem Configuration.isWOffenderAt (c : Configuration T D g) :
    IsWOffenderAt D.fullModule (T : Subgroup G) g := by
  refine ⟨c.noncommuting, ?_⟩
  simpa only [offenderNormalizer, source_fullModule_normalizer D] using c.attained

/-- The actual offender satisfies the strict inequality needed for E.3.31--32. -/
theorem Configuration.globalW_lt_globalR (c : Configuration T D g) :
    globalW D.fullModule (T : Subgroup G) < globalR D.fullModule := by
  have hw : globalW D.fullModule (T : Subgroup G) ≤ 2 := by
    rw [c.attained]
    exact_mod_cast c.small
  exact lt_of_le_of_lt hw ((by decide : (2 : ℕ∞) < 3).trans_le
    (source_fullModule_globalR_three_of_element_centralizers D c.pointCentralizers))

/-- The centralizer of the whole small offender is contained in the literal
conjugate maximal local subgroup; this does not assert that V lies there. -/
theorem Configuration.offender_centralizer_le_conjugate_maximal
    (c : Configuration T D g) :
    centralizer ((D.fullModule.map (MulAut.conj g).toMonoidHom ⊓
      D.maximalLocal : Subgroup G) : Set G) ≤
      D.maximalLocal.map (MulAut.conj g).toMonoidHom := by
  have hbound : (subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) : ℕ∞) <
      globalR (D.fullModule.map (MulAut.conj g).toMonoidHom) := by
    rw [globalR_map_equiv, ← c.attained]
    exact c.globalW_lt_globalR
  have h := centralizer_le_normalizer_of_corank_lt_globalR inf_le_left hbound
  rwa [← map_equiv_normalizer_eq D.fullModule (MulAut.conj g),
    source_fullModule_normalizer D] at h

end CFSG.Quasithin.Chapter10.SmallOffender
