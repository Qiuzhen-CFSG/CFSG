module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Definitions
public import Theory.GroupTheory.SylowImageIntersection
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SylowNormalizerCentralQuotient

/-!
# Lifting the selected Borel to the original component

The intersection S ∩ L is Sylow in L. Its image is exactly S⁺ ∩ L⁺,
by Sylow maximality, even though the full centralizer quotient need not
have central kernel. Restricted to L that kernel is precisely Z(L).
The central-kernel normalizer theorem therefore lifts containment in
the quotient Borel to containment in the intrinsic Borel of L.

No restriction on the order of Z(L) is needed, and the resulting Borel
includes the actual Sylow marking required by `BorelOverSylow`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the first
paragraph of the final proof of 15.3.35, printed p.1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection

variable {G : Type*} [Group G] [Finite G]
variable (L S : Subgroup G) [L.Normal] (P : Sylow 2 G) (hP : (P : Subgroup G) = S)

include P hP

/-- The intrinsic normalizer has the required actual Sylow marking. -/
theorem borelOverSylow : BorelOverSylow L S (sylowBorel L S) := by
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal L
  rw [hP] at hR
  refine ⟨R, ?_, ?_⟩
  · rw [hR, subgroupOf_map_subtype]
  · change sylowBorel L S = (normalizer ((R : Subgroup L) : Set L)).map L.subtype
    rw [hR]
    rfl

/-- The marked Sylow intersection commutes with the component-action quotient. -/
theorem component_sylow_image :
    (S.subgroupOf L).map ((centralizerQuotientMap L).subgroupMap L) =
      (S.map (centralizerQuotientMap L)).subgroupOf (centralizerQuotientComponent L) := by
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal L
  have hi := P.map_image_eq_inf L ((P : Subgroup G) ⊓ L) R
    (by rw [hR, subgroupOf_map_subtype]) inf_le_left (centralizerQuotientMap L)
  rw [hP] at hi
  ext d
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · intro hd
    have hdi : (d : CentralizerQuotient L) ∈ (S ⊓ L).map (centralizerQuotientMap L) :=
      hi ▸ ⟨hd, d.property⟩
    obtain ⟨x, ⟨hxS, hxL⟩, he⟩ := hdi
    exact ⟨⟨x, hxL⟩, hxS, Subtype.ext he⟩

/-- The quotient Borel pulls back to the Sylow normalizer inside L.
Only the restricted map has central kernel; no such assertion is made
about the whole map I → I/C_I(L). -/
theorem component_borel_preimage :
    ((sylowBorel (centralizerQuotientComponent L)
      (S.map (centralizerQuotientMap L))).subgroupOf (centralizerQuotientComponent L)).comap
        ((centralizerQuotientMap L).subgroupMap L) = normalizer (S.subgroupOf L : Set L) := by
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal L
  rw [hP] at hR
  have h := R.normalizer_comap_of_central_kernel
    ((centralizerQuotientMap L).subgroupMap L)
    ((centralizerQuotientMap L).subgroupMap_surjective L)
    (centralizerQuotient_component_ker L).le
  rw [sylowBorel, subgroupOf, comap_map_eq_self_of_injective
    (centralizerQuotientComponent L).subtype_injective]
  rw [← component_sylow_image L S P hP]
  change (normalizer
    (((R : Subgroup L).map ((centralizerQuotientMap L).subgroupMap L)) :
      Set (L.map (centralizerQuotientMap L)))).comap
        ((centralizerQuotientMap L).subgroupMap L) =
          normalizer ((R : Subgroup L) : Set L) at h
  rwa [hR] at h

/-- Containment in the quotient Borel lifts through the centralizer quotient. -/
theorem le_borel_of_image_le {Y : Subgroup G} (hYL : Y ≤ L)
    (hY : Y.map (centralizerQuotientMap L) ≤
      sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L))) :
    Y ≤ sylowBorel L S := by
  intro y hy
  have him : (⟨y, hYL hy⟩ : L) ∈
      ((sylowBorel (centralizerQuotientComponent L)
        (S.map (centralizerQuotientMap L))).subgroupOf (centralizerQuotientComponent L)).comap
        ((centralizerQuotientMap L).subgroupMap L) := hY (mem_map_of_mem _ hy)
  rw [component_borel_preimage L S P hP] at him
  exact ⟨⟨y, hYL hy⟩, him, rfl⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
