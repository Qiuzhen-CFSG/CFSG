module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondarySource
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryRadical

/-!+# Core and action geometry for the corrected secondary interface

The source core identity identifies Q with O₂(K). The component core lies
in the literal radical, and strict component containment detects its nontrivial
action without using the record's action field. Movement of Q transports to
the same normal quotient action used by the sieve.

The candidate Q[R₂,K₂]=R₂ has a necessary ambient condition: R₂≤K.
Indeed the secondary commutator is contained in O₂(K₂), and hence in K.
This keeps the possible part of R₂ outside K visible. No whole-radical
generation or equality R₂=O₂(K₂) is asserted here.

Source: Aschbacher--Smith, original 4.3.11--15, pp.617--618. The remaining
source construction and generation calculation belong to
`qt-d-1222-rankone-uniqueness-nonblock`.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

namespace SecondarySourceData

theorem core_eq_original (s : SecondarySourceData c n) : Q c = (K c).pCoreIn 2 := by
  have hn : K c ⊔ S c ≤ normalizer (K c : Set G) :=
    sup_le (K c).le_normalizer (inf_le_right.trans c.normalizer_component.le)
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp ((K c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c))))
  · exact (pCoreIn_mono_of_normalizes le_sup_left hn).trans_eq s.core_eq

theorem component_normalized (s : SecondarySourceData c n) :
    rootNormalizer c ≤ normalizer (s.component.map (rootNormalizer c).subtype : Set G) := by
  let := s.normal
  have hh := s.component.le_normalizer_map (rootNormalizer c).subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh

theorem component_core_le (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (s.component.map (rootNormalizer c).subtype).pCoreIn 2 ≤ R₂ c :=
  (pCoreIn_mono_of_normalizes le_sup_left
    ((sup_le (map_subtype_le _) (root_normalized c D)).trans s.component_normalized)).trans
      s.enlarged_core_le

theorem secondary_ne_bot_from_model (s : SecondarySourceData c n) : secondary c ≠ ⊥ := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := s.secondary_model
  let : Nontrivial (secondary c ⧸ pCore 2 (secondary c)) := e.surjective.nontrivial
  let : Nontrivial (secondary c) := (QuotientGroup.mk'_surjective (pCore 2 (secondary c))).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance

/-- The geometry proves nontriviality independently of the stored action clause. -/
theorem radical_action_from_geometry [Finite G] (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ((R₂ c).subgroupOf (rootNormalizer c)).map s.action ≠ ⊥ :=
  secondary_radical_action_of_strict_component D s.secondary_ne_bot_from_model
    s.component s.isComponent s.normal s.secondary_lt s.enlarged_core_le
    s.radical_le (s.radical_normalizer.trans inf_le_right)

/-- Core movement survives in the literal full-quotient action. -/
theorem core_action_moved [Finite G] (s : SecondarySourceData c n) :
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
theorem core_action_eq_bot_of_torus_action_eq_bot [Finite G] (s : SecondarySourceData c n)
    (hY : (s.torus.subgroupOf (rootNormalizer c)).map s.action = ⊥) :
    ((Q c).subgroupOf (rootNormalizer c)).map s.action = ⊥ := by
  rw [← s.core_action_moved, hY, commutator_bot_right]

end SecondarySourceData

/-- Every radical/secondary commutator belongs to the actual secondary two-core. -/
theorem radical_secondary_commutator_le_core
    (D : Chapter12.Section02.ChosenModule T L V) :
    ⁅R₂ c, secondary c⁆ ≤ (secondary c).pCoreIn 2 := by
  have hnorm : R₂ c ≤ normalizer (secondary c : Set G) :=
    (pCoreIn_le 2 _).trans (sup_le (secondary c).le_normalizer (sylow_normalizes_secondary D))
  have hKnorm : secondary c ≤ normalizer (R₂ c : Set G) :=
    (le_sup_left : secondary c ≤ secondary c ⊔ S c).trans
      ((secondary c ⊔ S c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 (secondary c ⊔ S c)).to_le
      (le_normalizer_iff_commutator_le_left.mp hKnorm))
    (le_normalizer_iff_commutator_le_right.mp hnorm)
    (normalizer_commutator_ge_right _ _)

/-- The proposed ambient generation identity must control the part outside K. -/
theorem radical_le_original_of_secondary_generation
    (D : Chapter12.Section02.ChosenModule T L V)
    (hgen : Q c ⊔ ⁅R₂ c, secondary c⁆ = R₂ c) : R₂ c ≤ K c := by
  rw [← hgen]
  exact sup_le
    ((le_normalizer_iff_commutator_le_left.mp ((K c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c))))).trans
        (pCoreIn_le 2 _))
    ((radical_secondary_commutator_le_core D).trans ((pCoreIn_le 2 _).trans secondary_le_original))

/-- Any proved ambient generation transports through the very same source action. -/
theorem SecondarySourceData.action_generation_of_generation [Finite G]
    (s : SecondarySourceData c n)
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
