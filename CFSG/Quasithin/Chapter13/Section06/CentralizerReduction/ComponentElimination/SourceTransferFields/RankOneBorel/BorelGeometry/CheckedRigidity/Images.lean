module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.QuotientIntersection

/-!
# The relative Borel under the checked quotient

The quotient kernel is contained in S because v belongs to S. This makes
images preserve the intersection K ∩ S. Since K is normalized by K S,
the relative normalizer also has the expected image. We apply this to
the literal map C_G(v) → C_G(v)/⟨v⟩, retaining the restricted subgroups
and relative Sylow condition.

Source: Aschbacher–Smith, proof of 13.6.18, printed p.931 (PDF p.948).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.CheckedRigidity
open Subgroup
open A5Module
variable {G H : Type*} [Group G] [Group H]

/-- The relative Borel survives a homomorphism whose kernel is contained in S. -/
theorem map_borel (f : G →* H) (K S : Subgroup G)
    (hSK : S ≤ normalizer (K : Set G)) (hker : f.ker ≤ S) :
    (borel K S).map f = borel (K.map f) (S.map f) := by
  have hi := map_inf_of_ker_le f K S hker
  apply le_antisymm
  · apply le_inf
    · simpa only [Subgroup.map_sup] using map_mono (f := f) (borel_le K S)
    · exact (map_mono (f := f) (show borel K S ≤ normalizer ((K ⊓ S : Subgroup G) : Set G)
        from inf_le_right)).trans (hi ▸ (K ⊓ S).le_normalizer_map f)
  · intro y hy
    have hyH : y ∈ (K ⊔ S).map f := by
      rw [Subgroup.map_sup]
      exact hy.1
    obtain ⟨x, hx, rfl⟩ := hyH
    refine mem_map.mpr ⟨x, ⟨hx, ?_⟩, rfl⟩
    have hxK : x ∈ normalizer (K : Set G) := (sup_le K.le_normalizer hSK) hx
    have hxP : x ∈ normalizer (((K ⊓ S).map f).comap f : Set G) := by
      apply ((K ⊓ S).map f).le_normalizer_comap f
      change f x ∈ normalizer ((K ⊓ S).map f : Set H)
      rw [hi]
      exact hy.2
    have he : K ⊓ ((K ⊓ S).map f).comap f = K ⊓ S := by
      apply le_antisymm
      · intro z hz
        refine ⟨hz.1, ?_⟩
        have hzS : z ∈ (S.map f).comap f := map_mono (f := f) inf_le_right hz.2
        rwa [comap_map_eq_self hker] at hzS
      · exact le_inf inf_le_left (le_comap_map f (K ⊓ S))
    rw [← he]
    exact inf_normalizer_le_normalizer_inf ⟨hxK, hxP⟩

/-- Restricting the Borel to an overgroup containing K and S is literal. -/
theorem borel_restrict (K S C : Subgroup G) (hK : K ≤ C) (hS : S ≤ C) :
    borel (K.subgroupOf C) (S.subgroupOf C) = (borel K S).subgroupOf C := by
  unfold borel
  change _ = ((K ⊔ S).subgroupOf C) ⊓ ((normalizer ((K ⊓ S : Subgroup G) : Set G)).subgroupOf C)
  rw [subgroupOf_sup hK hS, subgroupOf_normalizer_eq (inf_le_left.trans hK)]
  rfl

/-- The actual checked kernel is in every subgroup containing the marked v. -/
theorem checked_kernel_le (v : G) (S : Subgroup G) (hvS : v ∈ S) :
    (checkedQuotientMap v).ker ≤ S.subgroupOf (Gv v) := by
  rw [checkedQuotientMap_kernel, ← line_subgroupOf]
  exact comap_mono (zpowers_le.mpr hvS)

/-- The checked Borel is the Borel of the checked component and Sylow image. -/
theorem checkedImage_borel (K S : Subgroup G) (v : G)
    (hK : K ≤ Gv v) (hS : S ≤ Gv v)
    (hSK : S ≤ normalizer (K : Set G)) (hvS : v ∈ S) :
    checkedImage v (borel K S) = borel (checkedImage v K) (checkedImage v S) := by
  unfold checkedImage
  rw [← borel_restrict K S (Gv v) hK hS]
  apply map_borel
  · exact (comap_mono hSK).trans (K.le_normalizer_comap (Gv v).subtype)
  · exact checked_kernel_le v S hvS

/-- The checked component remains normalized by the checked Sylow image. -/
theorem checked_normalizes (K S : Subgroup G) (v : G)
    (hSK : S ≤ normalizer (K : Set G)) :
    checkedImage v S ≤ normalizer (checkedImage v K : Set (Gcheck v)) :=
  (map_mono ((comap_mono hSK).trans (K.le_normalizer_comap (Gv v).subtype))).trans
    ((K.subgroupOf (Gv v)).le_normalizer_map (checkedQuotientMap v))

variable [Finite G]
/-- Relative Sylow membership passes through the literal checked maps. -/
theorem checked_sylow (K S : Subgroup G) (v : G)
    (hK : K ≤ Gv v) (hS : S ≤ Gv v)
    (hSylow : Chapter1.IsSylowIn 2 S (K ⊔ S)) :
    Chapter1.IsSylowIn 2 (checkedImage v S) (checkedImage v K ⊔ checkedImage v S) := by
  have hrel : Chapter1.IsSylowIn 2 (S.subgroupOf (Gv v))
      ((K ⊔ S).subgroupOf (Gv v)) := by
    apply (Chapter1.IsSylowIn.map_iff (Gv v).subtype (Gv v).subtype_injective).mp
    rwa [map_subgroupOf_eq_of_le hS, map_subgroupOf_eq_of_le (sup_le hK hS)]
  have hm := Chapter1.Section02.IndexTwo.isSylowIn_map hrel (checkedQuotientMap v)
  rwa [subgroupOf_sup hK hS, Subgroup.map_sup] at hm
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.CheckedRigidity
