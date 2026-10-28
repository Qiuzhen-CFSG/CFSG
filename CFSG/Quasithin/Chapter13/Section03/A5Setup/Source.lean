module

public import CFSG.Quasithin.Chapter13.Section03.A5Setup.MarkedSource
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.Invariance
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalNormality
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Selecting the A₅ source flag and applying its local setup

The original natural A₅ module has order sixteen. As a normal subgroup of
the actual Sylow two-group it admits a nested normal flag of orders two,
four and eight. Transporting those very subgroups into G supplies every
flag field of the A₅ Context. The existing local-action theorem then gives
the literal equality C_T(V)=O₂(LT) and reducedness of V.

The source input is the original chosen Irr⁺ module and the one-or-two-copy
conclusion of the earlier module branch. Homogeneity of that chosen section
supplies its T-invariance. Neither a marked Context, normalizer action,
invariance, flag selection nor local-core equality is an additional premise.
Final source assembly must still prove the earlier module selection and
its stated classification.
Source: Aschbacher–Smith 13.3.2(3), Notation 13.2.1 and 13.2.3(1),
printed pp.885 and877–878.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem normal_map_normalized (B : Subgroup T) [B.Normal] :
    (T : Subgroup G) ≤ normalizer (B.map (T : Subgroup G).subtype : Set G) := by
  intro t ht
  apply le_normalizer_map (T : Subgroup G).subtype
  exact ⟨⟨t, ht⟩, by rw [normalizer_eq_top]; exact mem_top _, rfl⟩

/-- The flag consists of actual subgroups of the original Sylow and V. -/
theorem exists_invariant_flag (hVT : V ≤ (T : Subgroup G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hV : Nat.card V = 16) :
    ∃ V₁ V₂ V₃ : Subgroup G,
      V₁ ≤ V₂ ∧ V₂ ≤ V₃ ∧ V₃ ≤ V ∧
      Nat.card V₁ = 2 ∧ Nat.card V₂ = 4 ∧ Nat.card V₃ = 8 ∧
      (T : Subgroup G) ≤ normalizer (V₁ : Set G) ∧
      (T : Subgroup G) ≤ normalizer (V₂ : Set G) ∧
      (T : Subgroup G) ≤ normalizer (V₃ : Set G) := by
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  let W := V.subgroupOf (T : Subgroup G)
  have hW : W.Normal := (normal_subgroupOf_iff_le_normalizer hVT).mpr hTV
  have hcW : Nat.card W = 2 ^ 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVT).toEquiv).trans hV
  obtain ⟨B₃, hB₃, h3W, hc3⟩ :=
    exists_normal_subgroup_card_pow_of_normal (p := 2) W hW hcW 3 (by decide)
  obtain ⟨B₂, hB₂, h23, hc2⟩ :=
    exists_normal_subgroup_card_pow_of_normal (p := 2) B₃ hB₃ hc3 2 (by decide)
  obtain ⟨B₁, hB₁, h12, hc1⟩ :=
    exists_normal_subgroup_card_pow_of_normal (p := 2) B₂ hB₂ hc2 1 (by decide)
  let := hB₁
  let := hB₂
  let := hB₃
  refine ⟨B₁.map (T : Subgroup G).subtype, B₂.map (T : Subgroup G).subtype,
    B₃.map (T : Subgroup G).subtype, map_mono h12, map_mono h23, ?_, ?_, ?_, ?_,
    normal_map_normalized B₁, normal_map_normalized B₂, normal_map_normalized B₃⟩
  · exact (map_mono h3W).trans_eq (map_subgroupOf_eq_of_le hVT)
  · exact (card_map_of_injective (T : Subgroup G).subtype_injective).trans hc1
  · exact (card_map_of_injective (T : Subgroup G).subtype_injective).trans hc2
  · exact (card_map_of_injective (T : Subgroup G).subtype_injective).trans hc3

/-- The original module alternative supplies the marked source Context and
its whole invariant flag, with no prescribed coordinate-position premise. -/
theorem exists_context_of_one_or_two_modules
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (d : Chapter12.Section02.ChosenModule T L V)
    (hmodel : Chapter6.Source.IsOneOrTwoA5Modules L V) :
    ∃ V₁ V₂ V₃ : Subgroup G, V₂ ≤ V₃ ∧
      Nonempty (Section05.A5Source.Context T L V V₁ V₂ V₃) := by
  have hsingle := d.one_a5_of_one_or_two hmodel
  have hTV := chosen_natural_module_invariant d hsingle
  have hc : Nat.card V = 16 := by
    obtain ⟨_, f, _⟩ := hsingle
    have hdim : Module.finrank (ZMod 2) (natural (Fin 5)) = 4 := by
      simpa using finrank_natural_odd (Fin 5) (by decide)
    have hn := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := natural (Fin 5))
    rw [Nat.card_zmod, hdim] at hn
    exact (Nat.card_congr f.toEquiv).trans hn
  obtain ⟨V₁, V₂, V₃, h12, h23, h3V, h1, h2, h3, hT1, hT2, hT3⟩ :=
    exists_invariant_flag d.le_sylow hTV hc
  exact ⟨V₁, V₂, V₃, h23, context_of_natural_module h d hsingle hTV
    h12 (h23.trans h3V) h1 h2 hT1 hT2 h3V h3 hT3⟩

/-- The original F.9 local setup consumes the constructed Context: its
reducedness and the exact Sylow-centralizer equality are now discharged. -/
theorem local_setup_of_one_or_two_modules
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (d : Chapter12.Section02.ChosenModule T L V)
    (hmodel : Chapter6.Source.IsOneOrTwoA5Modules L V) :
    IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) ∧
      (T : Subgroup G) ⊓ centralizer (V : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨V₁, V₂, V₃, _, ⟨s⟩⟩ := exists_context_of_one_or_two_modules h d hmodel
  exact ⟨s.reduced, s.sylow_centralizer d.sylow_normalizes_component⟩

/-- The actual earlier rank-one output is stated on [V,L]. The original
Irr⁺ commutator identity identifies that layer with V before the construction. -/
theorem exists_context_of_layer_modules
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (d : Chapter12.Section02.ChosenModule T L V)
    (hmodel : Chapter6.Source.IsOneOrTwoA5Modules L (Chapter6.Source.layer L V)) :
    ∃ V₁ V₂ V₃ : Subgroup G, V₂ ≤ V₃ ∧
      Nonempty (Section05.A5Source.Context T L V V₁ V₂ V₃) := by
  change Chapter6.Source.IsOneOrTwoA5Modules L ⁅V,L⁆ at hmodel
  rw [← d.eq_commutator] at hmodel
  exact exists_context_of_one_or_two_modules h d hmodel

end CFSG.Quasithin.Chapter13.Section03.A5Setup
