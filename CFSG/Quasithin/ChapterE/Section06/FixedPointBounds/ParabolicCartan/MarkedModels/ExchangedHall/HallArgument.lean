module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Construction
public import Theory.GroupTheory.Hall.TwoCoreSection
public import Theory.GroupTheory.PCoreImage

/-!
# Applying normal-section Hall control inside the maximal overgroup

Restriction gives the actual Sylow subgroup of M and a normal subgroup
N ≤ M. Apply the finite-group normal-section theorem and map its literal
factorization back along M's inclusion. The resulting Q is the embedded
intrinsic two-core of M; its normalization is proved via characteristicity.

Source: Aschbacher--Smith, E.6.27, p.257, and 4.4.13(2), pp.623--624.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedHall
variable {G : Type*} [Group G] [Finite G]

/-- Apply the normal-section Hall theorem inside the actual maximal
overgroup and transport the factorization to the original ambient carrier. -/
theorem hallControl_of_normal_section (S : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (N : Subgroup G) (hNM : N ≤ ChapterB.minimalParabolicMax S hP)
    (hn : ChapterB.minimalParabolicMax S hP ≤ normalizer (N : Set G))
    (hgen : N ⊔ (S : Subgroup G) = ChapterB.minimalParabolicMax S hP)
    (hd : ⁅N, N⁆ ≤ (ChapterB.minimalParabolicMax S hP).pCoreIn 2) :
    HallControl S hP := by
  let M := ChapterB.minimalParabolicMax S hP
  have hSM : (S : Subgroup G) ≤ M := (ChapterB.minimalParabolicMax_spec S hP).2
  let : (N.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hn
  have hg : N.subgroupOf M ⊔ (S.subtype hSM : Subgroup M) = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hNM,
      ← MonoidHom.range_eq_map, range_subtype]
    change N ⊔ ((S : Subgroup G).subgroupOf M).map M.subtype = M
    rwa [map_subgroupOf_eq_of_le hSM]
  have hd' : ⁅N.subgroupOf M, N.subgroupOf M⁆ ≤ pCore 2 M := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hNM]
    exact hd
  obtain ⟨hs, hHall⟩ := Subgroup.OddHall.control_of_normal_abelian_section (S.subtype hSM) (N.subgroupOf M) hg hd'
  refine ⟨hs, ?_, ?_⟩
  · intro Y hYM hY
    let := (hHall (Y.subgroupOf M) hY).1
    let e := subgroupOfEquivOfLe hYM
    exact ⟨⟨fun a b => e.symm.injective (by simp only [map_mul, mul_comm])⟩⟩
  · intro Y hYM hY
    refine ⟨M.pCoreIn 2, ?_, ?_⟩
    · exact hYM.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M)))
    · have hh := congrArg (Set.image M.subtype) (hHall (Y.subgroupOf M) hY).2
      rw [Set.image_mul] at hh
      change (((S : Subgroup G).subgroupOf M).map M.subtype : Set G) =
        (M.pCoreIn 2 : Set G) *
        (((S.subtype hSM : Subgroup M) ⊓ normalizer (Y.subgroupOf M : Set M)).map
          M.subtype : Set G) at hh
      rw [map_subgroupOf_eq_of_le hSM] at hh
      have he : ((S.subtype hSM : Subgroup M) ⊓ normalizer (Y.subgroupOf M : Set M)).map
          M.subtype = (S : Subgroup G) ⊓ normalizer (Y : Set G) := by
        rw [← subgroupOf_normalizer_eq hYM]
        change (((S : Subgroup G) ⊓ normalizer (Y : Set G)).subgroupOf M).map M.subtype = _
        exact map_subgroupOf_eq_of_le (inf_le_left.trans hSM)
      rwa [he] at hh


end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedHall
