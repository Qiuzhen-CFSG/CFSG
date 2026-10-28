module

public import Theory.AtlasPort.LinearGroups.G2.EvenBorelTorus
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable.Borel
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.SylowAlignment
public import Theory.GroupTheory.Hall.Conjugacy

/-!
# Aligning the split torus inside the Sylow normalizer

An automorphism preserving the positive-root Sylow also preserves its Borel
normalizer. The split torus is an odd Hall subgroup of that concrete solvable
Borel. Hall conjugacy supplies a Borel element correcting the automorphism to
preserve both the Sylow subgroup and the torus. In particular it still fixes
both labelled parabolics. This step includes the field of order four.

This is an intermediate step toward root-frame alignment, not an automorphism
classification. Source context: the G₂ automorphism input in
Aschbacher--Smith F.1.12, printed pp.263--264. The concrete Borel and torus
are from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup
namespace Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
open LieParabolicSetup EvenBorelTorus
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem torus_hall :
    IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} (complement (F := F)) := by
  refine ⟨?_, ?_⟩
  · intro p hp he
    have hc : Nat.card (complement (F := F)) = Nat.card (splitTorus (K := F)) :=
      Nat.card_congr (subgroupOfEquivOfLe
        (show splitTorus (K := F) ≤ borel from le_sup_right)).toEquiv
    rw [he, hc] at hp
    exact card_torus_odd.not_two_dvd_nat hp
  · intro p hp hne
    rw [radical_isComplement.index_eq_card] at hp
    obtain ⟨n, hn⟩ := radical_isTwoGroup (F := F) |>.exists_card_eq
    rw [hn] at hp
    exact hne ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow hp))

/-- An inner correction in the actual Borel aligns its torus and preserves its Sylow. -/
theorem exists_sylow_torus_alignment (a : MulAut (Model F))
    (ha : unipotent.map a.toMonoidHom = unipotent) :
    ∃ g : Model F, g ∈ borel ∧
      unipotent.map (MulAut.conj g * a).toMonoidHom = unipotent ∧
      splitTorus.map (MulAut.conj g * a).toMonoidHom = splitTorus := by
  have hB : borel.map a.toMonoidHom = borel := by
    rw [← SylowNormalizer.normalizer_unipotent, map_equiv_normalizer_eq, ha]
  let b : MulAut (borel (K := F)) :=
    (a.subgroupMap borel).trans (MulEquiv.subgroupCongr hB)
  obtain ⟨g, hg⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable
    (DerivedNormalizerSolvable.isSolvable_borel (F := F))
    (torus_hall.map_mulAut b) torus_hall
  refine ⟨g, g.property, ?_, ?_⟩
  · change unipotent.map ((MulAut.conj (g : Model F)).toMonoidHom.comp a.toMonoidHom) = _
    rw [← map_map, ha]
    apply mem_normalizer_iff_map_conj_eq.mp
    rw [SylowNormalizer.normalizer_unipotent]
    exact g.property
  · have hs := congrArg (Subgroup.map (borel (K := F)).subtype) hg
    simp only [map_map] at hs
    change (complement (F := F)).map (borel (K := F)).subtype =
      (complement (F := F)).map
        ((MulAut.conj (g : Model F) * a).toMonoidHom.comp
          (borel (K := F)).subtype) at hs
    rw [← map_map,
      map_subgroupOf_eq_of_le (show splitTorus (K := F) ≤ borel from le_sup_right)] at hs
    exact hs.symm
end Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
