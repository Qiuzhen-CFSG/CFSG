module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceData
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondarySourceGeometry

/-!
# Core geometry for the source action data

The literal component core lies in R₂, and the original core movement and
radical generation pass to the full quotient action. These proofs transfer
NonblockSecondarySourceGeometry using only its geometric and action clauses;
none uses strict enlargement or universal movement by the torus.
Source: Aschbacher–Smith, original 4.3.11–15, printed pp.617–618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

namespace SecondaryActionData

theorem core_eq_original (s : SecondaryActionData c n) : Q c = (K c).pCoreIn 2 := by
  have hn : K c ⊔ S c ≤ normalizer (K c : Set G) :=
    sup_le (K c).le_normalizer (inf_le_right.trans c.normalizer_component.le)
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp ((K c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c))))
  · exact (pCoreIn_mono_of_normalizes le_sup_left hn).trans_eq s.core_eq

theorem component_normalized (s : SecondaryActionData c n) :
    rootNormalizer c ≤ normalizer (s.component.map (rootNormalizer c).subtype : Set G) := by
  let := s.normal
  have hh := s.component.le_normalizer_map (rootNormalizer c).subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh

theorem component_core_le (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (s.component.map (rootNormalizer c).subtype).pCoreIn 2 ≤ R₂ c :=
  (pCoreIn_mono_of_normalizes le_sup_left
    ((sup_le (map_subtype_le _) (root_normalized c D)).trans s.component_normalized)).trans
      s.enlarged_core_le

theorem secondary_ne_bot_from_model (s : SecondaryActionData c n) : secondary c ≠ ⊥ := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := s.secondary_model
  let : Nontrivial (secondary c ⧸ pCore 2 (secondary c)) := e.surjective.nontrivial
  let : Nontrivial (secondary c) := (QuotientGroup.mk'_surjective (pCore 2 (secondary c))).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance

/-- The geometry proves nontriviality independently of the stored action clause. -/
theorem radical_action_from_geometry [Finite G] (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ((R₂ c).subgroupOf (rootNormalizer c)).map s.action ≠ ⊥ :=
  secondary_radical_action_of_strict_component D s.secondary_ne_bot_from_model
    s.component s.isComponent s.normal s.secondary_lt s.enlarged_core_le
    s.radical_le (s.radical_normalizer.trans inf_le_right)

/-- Core movement survives in the literal full-quotient action. -/
theorem core_action_moved [Finite G] (s : SecondaryActionData c n) :
    ⁅((Q c).subgroupOf (rootNormalizer c)).map s.action,
      (s.torus.subgroupOf (rootNormalizer c)).map s.action⁆ =
      ((Q c).subgroupOf (rootNormalizer c)).map s.action := by
  have hQ : Q c ≤ rootNormalizer c := (core_le_radical c).trans s.radical_le
  have he : ⁅(Q c).subgroupOf (rootNormalizer c),
      s.torus.subgroupOf (rootNormalizer c)⁆ = (Q c).subgroupOf (rootNormalizer c) := by
    apply map_injective (rootNormalizer c).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hQ,
      map_subgroupOf_eq_of_le s.torus_le, s.core_moved]
  rw [← map_commutator, he]

/-- A trivial torus image kills Q's image; it does not by itself kill R₂'s image. -/
theorem core_action_eq_bot_of_torus_action_eq_bot [Finite G] (s : SecondaryActionData c n)
    (hY : (s.torus.subgroupOf (rootNormalizer c)).map s.action = ⊥) :
    ((Q c).subgroupOf (rootNormalizer c)).map s.action = ⊥ := by
  rw [← s.core_action_moved, hY, commutator_bot_right]

end SecondaryActionData

/-- Any proved ambient generation transports through the very same source action. -/
theorem SecondaryActionData.action_generation_of_generation [Finite G]
    (s : SecondaryActionData c n)
    (hgen : Q c ⊔ ⁅R₂ c, secondary c⁆ = R₂ c) :
    ((Q c).subgroupOf (rootNormalizer c)).map s.action ⊔
      ⁅((R₂ c).subgroupOf (rootNormalizer c)).map s.action,
        ((secondary c).subgroupOf (rootNormalizer c)).map s.action⁆ =
      ((R₂ c).subgroupOf (rootNormalizer c)).map s.action := by
  have hQ : Q c ≤ rootNormalizer c := (core_le_radical c).trans s.radical_le
  have hK : secondary c ≤ rootNormalizer c := s.secondary_le.trans (map_subtype_le _)
  have he : (Q c).subgroupOf (rootNormalizer c) ⊔
      ⁅(R₂ c).subgroupOf (rootNormalizer c), (secondary c).subgroupOf (rootNormalizer c)⁆ =
      (R₂ c).subgroupOf (rootNormalizer c) := by
    apply map_injective (rootNormalizer c).subtype_injective
    rw [Subgroup.map_sup, map_commutator, map_subgroupOf_eq_of_le hQ,
      map_subgroupOf_eq_of_le s.radical_le, map_subgroupOf_eq_of_le hK, hgen]
  rw [← map_commutator, ← Subgroup.map_sup, he]

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
