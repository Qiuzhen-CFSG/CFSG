module
public import CFSG.Quasithin.Chapter10.SourceNormalizationSurvivor
public import Theory.GroupTheory.PerfectSylowPreservingAction
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson.Transport

/-!
# Parameter-one generation in the original linear-three survivor

The natural moved section has order eight, hence r(G,V)≥3, while w(G,V)=2.
The overgroup generation bound therefore puts every parameter-one overgroup
of T in M. The Sylow normalizer is solvable and also lies in M. Applying
these statements to the original embeddings of minimal parabolics proves
the containment assertion at the start of 10.3.3.

Source: Aschbacher--Smith 10.2.9, 10.2.13 and 10.3.3, printed pp.750,755--756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreeSurvivor T D)
include s

private theorem survivor_globalR_three : (3 : ℕ∞) ≤ globalR D.fullModule := by
  have hcard := s.natural.card_section
  have hn : 0 < Nat.card (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) : Subgroup G) :=
    Nat.card_pos
  have hsize : 8 ≤ Nat.card (⁅D.fullModule,L⁆ : Subgroup G) := by
    simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at hcard
    norm_num at hcard
    change Nat.card (⁅D.fullModule,L⁆ : Subgroup G) =
      8 * Nat.card (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) : Subgroup G) at hcard
    omega
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hr := source_fullModule_globalR_lower_of_element_centralizers D
    (le_normalizer_iff_commutator_le_left.mp hLV) s.pointCentralizers
  have hlog : 3 ≤ Nat.log 2 (Nat.card (⁅D.fullModule,L⁆ : Subgroup G)) := by
    have := Nat.log_mono_right (b := 2) hsize
    norm_num at this
    exact this
  exact le_trans (by exact_mod_cast hlog) hr

/-- Parameter one is incompatible with escape from the original M. -/
theorem generation_one_overgroups_le {Y : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) (hn : generationParameter Y = 1) :
    Y ≤ D.maximalLocal := by
  by_contra hout
  have hb := source_overgroup_generation_bound D hTY hout (by omega)
  rw [s.weakClosure, hn] at hb
  rcases min_le_iff.mp hb with hw | hr
  · exact (by decide : ¬ (2 : ℕ∞) ≤ 1) hw
  · exact (by decide : ¬ (3 : ℕ∞) ≤ 1) ((survivor_globalR_three s).trans hr)

/-- Solvability puts the original Sylow normalizer in M. -/
theorem sylow_normalizer_le : normalizer (T : Set G) ≤ D.maximalLocal := by
  let := T.normalizer_isSolvable_two
  exact s.solvable_overgroups_le (T : Subgroup G).le_normalizer

private theorem generation_one_subgroups_le {Y : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) (P : Subgroup Y)
    (hTP : ((T.subtype hTY : Sylow 2 Y) : Subgroup Y) ≤ P)
    (hn : generationParameter P = 1) : P.map Y.subtype ≤ D.maximalLocal := by
  apply generation_one_overgroups_le s
  · have hh := map_mono (f := Y.subtype) hTP
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTY] using hh
  · rw [← ChapterE.Section06.FixedPointBounds.SylowThompson.generationParameter_equiv
      (P.equivMapOfInjective Y.subtype Y.subtype_injective)]
    exact hn

/-- The opening containment argument of 10.3.3, for a specified generating
family, retaining the intrinsic normalizer and original Sylow embeddings. -/
theorem minimal_parabolic_family_generated_le {Y : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) (Δ : Set (Subgroup Y))
    (hΔ : ∀ P ∈ Δ, ChapterB.IsMinimalParabolicOver (T.subtype hTY) P ∧
      generationParameter P = 1)
    (hgen : sSup Δ ⊔ normalizer (T.subtype hTY : Set Y) = ⊤) :
    Y ≤ D.maximalLocal := by
  have hall : (⊤ : Subgroup Y) ≤ D.maximalLocal.subgroupOf Y := by
    rw [← hgen]
    apply sup_le
    · apply sSup_le
      intro P hP
      exact (map_le_iff_le_comap).mp
        (generation_one_subgroups_le s hTY P (hΔ P hP).1.1.1.le (hΔ P hP).2)
    · change normalizer ((T : Subgroup G).subgroupOf Y : Set Y) ≤ _
      rw [← subgroupOf_normalizer_eq hTY]
      exact comap_mono (f := Y.subtype) (sylow_normalizer_le s)
  intro y hy
  exact hall (mem_top (⟨y, hy⟩ : Y))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
