module
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxGlobal

/-!
# Elementary Thompson containment for Sylow overgroups

An intermediate subgroup containing a Sylow two-subgroup has the same
maximum elementary abelian order as the ambient group: Sylow conjugacy
moves any elementary two-subgroup into the intermediate subgroup. Thus
its elementary Thompson subgroup lies in the ambient Thompson subgroup.
-/
public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- Containment of a full Sylow two-subgroup makes the elementary Thompson
subgroup monotone up to the whole group. -/
theorem elementaryAbelianMaxJ_le_top_of_contains_sylow
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H) :
    elementaryAbelianMaxJ H ≤ elementaryAbelianMaxJ (⊤ : Subgroup G) := by
  apply sSup_le
  intro A hA
  apply le_sSup
  refine ⟨le_top,hA.2.1,?_⟩
  intro B _ hB
  obtain ⟨P,hBP⟩ := hB.isPGroup.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P S
  let a := MulAut.conj g
  have hPS : (P : Subgroup G).map a.toMonoidHom = (S : Subgroup G) := by
    change ((g • P : Sylow 2 G) : Subgroup G) = (S : Subgroup G)
    rw [hg]
  have hBH : B.map a.toMonoidHom ≤ H := (map_mono hBP).trans (hPS.le.trans hSH)
  have hh := hA.2.2 (B.map a.toMonoidHom) hBH (hB.map a.toMonoidHom)
  rwa [card_map_of_injective a.injective] at hh

/-- The literal elementary Thompson subgroups are monotone between two
subgroups when the smaller one contains a Sylow two-subgroup of the larger. -/
theorem elementaryAbelianMaxJ_mono_of_contains_sylow
    (H K : Subgroup G) (hHK : H ≤ K) (S : Sylow 2 K)
    (hSH : (S : Subgroup K).map K.subtype ≤ H) :
    elementaryAbelianMaxJ H ≤ elementaryAbelianMaxJ K := by
  have hh := map_mono (f := K.subtype)
    (elementaryAbelianMaxJ_le_top_of_contains_sylow S (H.subgroupOf K)
      (fun x hx => hSH (mem_map_of_mem K.subtype hx)))
  rw [←elementaryAbelianMaxJ_map_injective K.subtype K.subtype_injective,
    ←elementaryAbelianMaxJ_map_injective K.subtype K.subtype_injective,
    map_subgroupOf_eq_of_le hHK,←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh

end Stellmacher
