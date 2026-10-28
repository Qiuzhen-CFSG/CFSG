module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.Geometry
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Stellmacher.BaumannNormalizer

/-!
# Common characteristic subgroups in the Cartan contradiction

Uniqueness of the maximal two-local over LT controls the normalizer of
every nontrivial two-subgroup normalized by L and T. The original residual
cannot also normalize it, since its Sylow supplement H escapes N_G(L).
In particular the common characteristic-subgroup alternative inside the
actual Baumann subgroup is impossible. The same uniqueness applied to
involution centralizers eliminates common fixed points in Ω₁Z(T).

Source: Aschbacher–Smith 5.1.13, printed pp.637–638, using 1.2.7.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
namespace Input
variable {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
  (h : Input KnownSimple.IsKnownSimple T L W n)
include h

/-- The two original components cannot normalize a common nontrivial
two-subgroup also normalized by the chosen Sylow subgroup. -/
theorem common_normalized_twoGroup_eq_bot
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hLQ : L ≤ normalizer (Q : Set G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hRQ : residual H ≤ normalizer (Q : Set G)) : Q = ⊥ := by
  by_contra hne
  have hn := normalizer_le_of_unique_maximalTwoLocal h.unique_local_join hQ hne (sup_le hLQ hTQ)
  exact residual_not_le T H (normalizer (L : Set G)) hH.1.1.2
    h.sylow_normalizes hH.1.2 (hRQ.trans hn)

/-- Characteristicness is inside the actual Baumann subgroup. The common
normal-subgroup alternative in the block argument is therefore impossible. -/
theorem common_characteristic_baumann_eq_bot
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (C : Subgroup (ChapterB.baumann (T : Subgroup G))) [C.Characteristic]
    (hLC : ((C.map (ChapterB.baumann (T : Subgroup G)).subtype).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal)
    (hRC : ((C.map (ChapterB.baumann (T : Subgroup G)).subtype).subgroupOf
      (residual H ⊔ (T : Subgroup G))).Normal) : C = ⊥ := by
  let B := ChapterB.baumann (T : Subgroup G)
  let Q := C.map B.subtype
  have hQT : Q ≤ (T : Subgroup G) := (map_subtype_le C).trans inf_le_left
  have hLn := (normal_subgroupOf_iff_le_normalizer (hQT.trans le_sup_right)).mp hLC
  have hRn := (normal_subgroupOf_iff_le_normalizer (hQT.trans le_sup_right)).mp hRC
  have hTn : (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (T : Subgroup G).le_normalizer.trans
      ((normalizer_le_normalizer_baumann (T : Subgroup G)).trans
        (normalizer_le_normalizer_characteristic_image B C))
  have he := h.common_normalized_twoGroup_eq_bot hH Q
    ((T.isPGroup'.to_le (show B ≤ (T : Subgroup G) from inf_le_left)).to_subgroup C |>.map B.subtype)
    (le_sup_left.trans hLn) hTn (le_sup_left.trans hRn)
  exact (C.map_eq_bot_iff_of_injective B.subtype_injective).mp he

/-- The original omega-center has no nonidentity element fixed by both
original components; uniqueness is applied to its involution centralizer. -/
theorem omega_common_fixed_eq_bot
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓
      centralizer (residual H : Set G) = ⊥ := by
  apply bot_unique
  intro z hz
  by_contra hne
  have hzone : z ≠ 1 := fun he => hne (mem_bot.mpr he)
  have hzt := (mem_omegaOneCenterAmbient_iff _ _).mp hz.1.1
  obtain ⟨N,hCN,hN⟩ := Finite.exists_le_maximal
    (isTwoLocal_involution_centralizer (orderOf_eq_prime hzt.2.1 hzone))
  have hLC : L ≤ centralizer ({z} : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hz.1.2 l hl)
  have hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hzt.2.2 t ht)
  have hRC : residual H ≤ centralizer ({z} : Set G) := by
    intro r hr
    exact mem_centralizer_singleton_iff.mpr (hz.2 r hr)
  have hNM := h.unique_local_join N hN ((sup_le hLC hTC).trans hCN)
  exact residual_not_le T H (normalizer (L : Set G)) hH.1.1.2
    h.sylow_normalizes hH.1.2 (hNM ▸ hRC.trans hCN)
end Input
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
