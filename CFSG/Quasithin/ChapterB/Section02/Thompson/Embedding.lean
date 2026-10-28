module
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.ElementaryAbelian.Injective
/-!
# Higher Thompson subgroups under group embeddings

Injective maps preserve the maximum elementary order and each rank-indexed
Thompson family. Mapping the defining supremum therefore commutes with every
higher Thompson subgroup. This retains the literal intrinsic-to-ambient
Sylow map in the E.6.26 application.
Source: Aschbacher–Smith B.2.2–3 and E.6.26, pp.74–75,256.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] [Finite H] in
private theorem elementary_comap_injective (f : G →* H) (hf : Function.Injective f)
    (B : Subgroup H) (he : IsElementaryAbelian 2 B) :
    IsElementaryAbelian 2 (B.comap f) := by
  let := he
  apply IsElementaryAbelian.of_injective (f.subgroupComap B)
  intro x y hxy
  exact Subtype.ext (hf (congrArg Subtype.val hxy))

theorem twoRank_map_injective (f : G →* H) (hf : Function.Injective f)
    (S : Subgroup G) : twoRank (S.map f) = twoRank S := by
  unfold twoRank
  congr 1
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty S
  obtain ⟨B,hB⟩ := elementaryAbelianMaxSubgroups_nonempty (S.map f)
  have hm : (B.comap f).map f = B := map_comap_eq_self (hB.1.trans (S.map_le_range f))
  have hBS : B.comap f ≤ S := by
    apply (map_le_map_iff_of_injective hf).mp
    rw [hm]
    exact hB.1
  apply le_antisymm
  · rw [← card_eq_elementaryAbelianMaxOrder _ B hB, ← hm, card_map_of_injective hf]
    exact hA.2.2 (B.comap f) hBS (elementary_comap_injective f hf B hB.2.1) |>.trans_eq
      (card_eq_elementaryAbelianMaxOrder _ A hA)
  · rw [← card_eq_elementaryAbelianMaxOrder _ A hA]
    have hc := hB.2.2 (A.map f) (map_mono hA.1) (hA.2.1.map f)
    rw [card_map_of_injective hf] at hc
    exact hc.trans_eq (card_eq_elementaryAbelianMaxOrder _ B hB)

theorem thompsonFamily_map_iff_of_injective (f : G →* H) (hf : Function.Injective f)
    (S A : Subgroup G) (i : ℕ) :
    A.map f ∈ thompsonFamily (S.map f) i ↔ A ∈ thompsonFamily S i := by
  constructor
  · intro h
    have he := elementary_comap_injective f hf (A.map f) h.2.1
    rw [comap_map_eq_self_of_injective hf] at he
    refine ⟨(map_le_map_iff_of_injective hf).mp h.1,he,?_,?_⟩
    · simpa only [twoRank_map_injective f hf] using h.2.2.1
    · simpa only [twoRank_map_injective f hf,card_map_of_injective hf] using h.2.2.2
  · intro h
    refine ⟨map_mono h.1,h.2.1.map f,?_,?_⟩
    · simpa only [twoRank_map_injective f hf] using h.2.2.1
    · simpa only [twoRank_map_injective f hf,card_map_of_injective hf] using h.2.2.2

theorem thompsonJ_map_injective (f : G →* H) (hf : Function.Injective f)
    (S : Subgroup G) (i : ℕ) :
    thompsonJ (S.map f) i = (thompsonJ S i).map f := by
  apply le_antisymm
  · apply sSup_le
    intro B hB
    have hm : (B.comap f).map f = B := map_comap_eq_self (hB.1.trans (S.map_le_range f))
    have hb : B.comap f ∈ thompsonFamily S i := by
      apply (thompsonFamily_map_iff_of_injective f hf S (B.comap f) i).mp
      rwa [hm]
    rw [← hm]
    exact map_mono (le_sSup hb)
  · apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro A hA
    exact map_le_iff_le_comap.mp (le_sSup
      ((thompsonFamily_map_iff_of_injective f hf S A i).mpr hA))
end CFSG.Quasithin.ChapterB

