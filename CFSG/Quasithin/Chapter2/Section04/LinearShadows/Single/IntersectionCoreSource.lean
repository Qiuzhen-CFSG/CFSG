module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedGeometrySource
public import Theory.GroupTheory.SylowNormalizerCentralizerCore
/-!
# The literal Borel intersection core

The original intersection M∩L is the normalizer of a Sylow subgroup of L.
Its two-core is therefore the embedded Sylow subgroup R. Since N_G(Z)
normalizes L in the nontrivial-center branch, N_M(Z) normalizes this core.

Source: Aschbacher–Smith, the last normality step of 2.4.20(4), p.535.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_intersection_two_core
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
 :
    twoCore (M ⊓ d.block.map d.H.subtype) =
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  obtain ⟨P,hP,hPN⟩ := source_intersection_borel d hsingle hL
  let f : d.block →* G := d.H.subtype.comp d.block.subtype
  have hf : Function.Injective f := d.H.subtype_injective.comp d.block.subtype_injective
  have hm : (normalizer (P:Set d.block)).map f=M⊓L := by
    rw [hPN]
    change (((M.subgroupOf d.H).subgroupOf d.block).map (d.H.subtype.comp d.block.subtype))=M⊓L
    rw [←map_map,subgroupOf_map_subtype, map_inf _ _ _ d.H.subtype_injective]
    have hMH : (M.subgroupOf d.H).map d.H.subtype=M⊓d.H := subgroupOf_map_subtype _ _
    rw [hMH,inf_assoc,inf_eq_right.mpr (map_subtype_le d.block)]
  have hcore := sylow_map_eq_pCoreIn_of_normalizer_map_eq P f hf (M⊓L) hm
  have hPR : (P : Subgroup d.block).map f=R := by
    rw [←map_map,hP,map_inf _ _ _ d.H.subtype_injective]
    exact (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).1.symm
  change (M⊓L).pCoreIn 2=R
  exact hcore.symm.trans hPR

/-- The normalizer of the distinguished subgroup inside M normalizes R. -/
theorem source_distinguished_normalizer_normalizes_thompson
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)

    (hz : center (d.block.map d.H.subtype) ≠ ⊥) :
    M ⊓ normalizer (distinguishedZ d : Set G) ≤
      normalizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G) := by
  let L := d.block.map d.H.subtype
  have hNL : normalizer (distinguishedZ d : Set G)=normalizer (L:Set G) :=
    (source_distinguished_TI_of_center_ne_bot d hG T hST hsingle hL hM hTM hunique hz).2.trans
      (lemma_2_4_11_1 d hG T hST hsingle hL hM hTM hunique)
  have hn : M ⊓ normalizer (distinguishedZ d : Set G)≤normalizer (M⊓L:Set G) := by
    rw [hNL]
    exact (le_inf (inf_le_left.trans M.le_normalizer) inf_le_right).trans
      inf_normalizer_le_normalizer_inf
  rw [←source_intersection_two_core d hG T hST hsingle hL hM hTM hunique]
  exact hn.trans (normalizer_le_normalizer_characteristic_image (M⊓L) (pCore 2 (M⊓L : Subgroup G)))
end CFSG.Quasithin.Chapter2.LinearShadows.Single
