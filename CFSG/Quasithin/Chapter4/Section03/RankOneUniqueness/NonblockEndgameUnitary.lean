module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSetup
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupAction.ExtraspecialQuinticCenter
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# The central quintic index contradiction in the nonblock endgame

The original root normalizer contains T and is a two-local, hence has
characteristic two. Its secondary component inherits a self-centralizing
two-core. Any actual extraspecial Sylow five-group in that component acts
faithfully on the two-core, forcing its center to have fixed index at
least 2^20. Relative normality puts this same two-core inside R₂.

The remaining inputs are deliberately separate: the parabolic calculation
must bound the actual quintic fixed index on R₂ by 2^16, and the unitary
geometry must identify the embedded center with an order-five subgroup
of the original K₂. Neither input is constructed by this module. The
conditional contradiction below consumes both with the original maps.

Source: Aschbacher--Smith, conclusion of original 4.3.2, printed p.618;
the characteristic-two inheritance is 1.1.3--4, printed pp.500--501.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- A Sylow five-group in the actual secondary component, whose embedded
center lies in the literal K₂. This is a construction target, not a source theorem. -/
structure UnitaryFiveMarking (s : SecondaryData c n) where
  actor : Subgroup G
  le_component : actor ≤ s.component.map (rootNormalizer c).subtype
  extraspecial : IsExtraspecial 5 actor
  card : Nat.card actor = 5 ^ 3
  center_le_secondary : (center actor).map actor.subtype ≤ secondary c
  sylow : ∃ P : Sylow 5 s.component,
    ((P : Subgroup s.component).map s.component.subtype).map (rootNormalizer c).subtype = actor

/-- The numerical consequence of the four nontrivial binary C₅ factors on R₂.
Its producer must use the natural and doubled-dual modules and the parabolic quotient. -/
def QuinticRadicalBound (c : SourceConfiguration T L) : Prop :=
  ∀ X : Subgroup G, X ≤ secondary c → Nat.card X = 5 →
    (centralizer (X : Set G)).relIndex (R₂ c) ≤ 2 ^ 16

/-- Characteristic two for the original secondary component, transported to G. -/
theorem unitaryFive_component_core_selfCentralizing (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let H := s.component.map (rootNormalizer c).subtype
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  have hlocal : IsTwoLocal (rootNormalizer c) := by
    let := c.c28.module_elementary
    exact ⟨root c, root_ne_bot c D,
      (IsElementaryAbelian.isPGroup 2 (W c)).to_le inf_le_left, rfl⟩
  have hchar : HasCharacteristicTwo (rootNormalizer c) :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) hlocal (root_normalized c D))
  have hc := subnormal_core_selfCentralizing hchar s.component s.isComponent.subnormal
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (s.component.equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective)).mp hc

omit [Finite G] in
/-- The embedded component core lies in the same R₂ used in the index bound. -/
theorem unitaryFive_component_core_le (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (s.component.map (rootNormalizer c).subtype).pCoreIn 2 ≤ R₂ c := by
  let := s.normal
  have hn : rootNormalizer c ≤ normalizer
      (s.component.map (rootNormalizer c).subtype : Set G) := by
    have hh := s.component.le_normalizer_map (rootNormalizer c).subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  exact (pCoreIn_mono_of_normalizes le_sup_left
    ((sup_le (map_subtype_le _) (root_normalized c D)).trans hn)).trans s.enlarged_core_le

/-- Conditional assembly of the central-index contradiction. Both the marked
Sylow construction and the parabolic bound remain separate source obligations. -/
theorem unitaryFive_false_of_marking_and_bound (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (m : UnitaryFiveMarking s) (hbound : QuinticRadicalBound c) : False := by
  let H := s.component.map (rootNormalizer c).subtype
  let C := H.pCoreIn 2
  let P := m.actor
  let : IsExtraspecial 5 P := m.extraspecial
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hc : H ⊓ centralizer (C : Set G) ≤ C := by
    intro x hx
    have hh : (⟨x,hx.1⟩ : H) ∈ centralizer (pCore 2 H : Set H) := by
      intro y hy
      apply Subtype.ext
      exact hx.2 y (mem_map_of_mem _ hy)
    exact mem_map_of_mem H.subtype (unitaryFive_component_core_selfCentralizing s D h hh)
  have hdis : P ⊓ C = ⊥ :=
    (IsPGroup.disjoint_of_ne 5 2 (by decide) P C
      (IsPGroup.of_card m.card) (isPGroup_pCoreIn 2 H)).eq_bot
  have hf : P ⊓ centralizer (C : Set G) = ⊥ :=
    bot_unique ((le_inf inf_le_left ((inf_le_inf_right _ m.le_component).trans hc)).trans_eq hdis)
  have hn : P ≤ normalizer (C : Set G) :=
    m.le_component.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hl := ExtraspecialQuinticCenter.centralizer_relIndex_lower_bound P C m.card
    (isPGroup_pCoreIn 2 H) hn hf
  have hX : Nat.card ((center P).map P.subtype) = 5 := by
    rw [card_map_of_injective P.subtype_injective]
    exact IsExtraspecial.center_order_p 5 P
  have hu := hbound _ m.center_le_secondary hX
  have hm := (centralizer ((center P).map P.subtype : Set G)).relIndex_le_of_le_right
    (unitaryFive_component_core_le s D)
    (Subgroup.FiniteIndex.index_ne_zero (H :=
      (centralizer ((center P).map P.subtype : Set G)).subgroupOf (R₂ c)))
  have hnum : 2 ^ 20 ≤ (2 : ℕ) ^ 16 := hl.trans (hm.trans hu)
  norm_num at hnum
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
