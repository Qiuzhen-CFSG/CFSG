module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.SylowCandidate
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.GroupTheory.PRadicalSylowNormalizer

/-!
# A local route to self-normalizing Sylow subgroups of J₄

The specified subgroup `OddIndex.twoSubgroup` is the full preimage of a
Sylow two-subgroup of the certified M₂₄ quotient of the ATLAS max1 subgroup.
If M₂₄ Sylow two-subgroups are self-normalizing, this preimage is
self-normalizing inside max1. Ambient normalizer containment then makes it
self-normalizing in J₄ itself. The normalizer condition proves ambient
Sylow maximality, and Sylow conjugacy transfers the result to every Sylow.

Both normalizer inputs remain explicit. In particular odd ambient index of
max1 alone is not substituted for containment of the ambient normalizer.
No ambient J₄ order calculation or assertion about outer automorphisms is used.

Source context: GLS3, Table 5.3i, in
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. The concrete quotient comparison is
proved in `LocalStructure.Mathieu`; the two-subgroup and its ATLAS provenance
are in `AutomorphismReduction.FirstGenerator.OddIndex.SylowCandidate`.
-/

public section

open Subgroup
open Janko4.Cardinality Janko4.OuterReduction.OddIndex
open scoped Pointwise

namespace Janko4.LocalStructure.SymmetricLinear

/-- Transfer actual normalizer control through the certified M₂₄ quotient.
The ambient-containment and M₂₄ inputs are separate proof obligations. -/
theorem sylowNormalizer_le_of_max1Normalizer
    (hambient : normalizer (twoSubgroup : Set Model) ≤
      max1Subgroup matrixA_mul_self matrixB_pow_four)
    (hM24 : ∀ S : Sylow 2 Sporadic.Mathieu.M24,
      normalizer (S : Set Sporadic.Mathieu.M24) ≤ S.toSubgroup) :
    ∀ S : Sylow 2 Model, normalizer (S : Set Model) ≤ S.toSubgroup := by
  let L := max1Subgroup matrixA_mul_self matrixB_pow_four
  let e := QuotientCount.Image.starGroupEquivM24
  let f : L →* Sporadic.Mathieu.M24 := e.toMonoidHom.comp localProjection
  have hf : Function.Surjective f := e.surjective.comp localProjection_surjective
  let T := localSylow.mapSurjective hf
  have hker : f.ker ≤ localTwoSubgroup := by
    intro x hx
    change e (localProjection x) = 1 at hx
    have hx' : localProjection x = 1 := e.injective (by
      simpa only [map_one] using hx)
    change localProjection x ∈ Simplicity.Max1Fusion.QuotientInvolutions.sylowCandidate
    rw [hx']
    exact one_mem _
  have hlocal : normalizer (localTwoSubgroup : Set L) ≤ localTwoSubgroup := by
    have hh := (localTwoSubgroup.le_normalizer_map f).trans (hM24 T)
    have hp := Subgroup.map_le_iff_le_comap.mp hh
    change normalizer (localTwoSubgroup : Set L) ≤
      (localTwoSubgroup.map f).comap f at hp
    simpa only [Subgroup.comap_map_eq_self hker] using hp
  have hself : normalizer (twoSubgroup : Set Model) = twoSubgroup := by
    apply le_antisymm _ twoSubgroup.le_normalizer
    intro g hg
    let g' : L := ⟨g, hambient hg⟩
    have hgn : g' ∈ normalizer (twoSubgroup.subgroupOf L : Set L) := by
      rw [← subgroupOf_normalizer_eq twoSubgroup_le]
      exact hg
    have hpull : twoSubgroup.subgroupOf L = localTwoSubgroup := by
      change (localTwoSubgroup.map L.subtype).comap L.subtype = localTwoSubgroup
      exact comap_map_eq_self_of_injective L.subtype_injective _
    rw [hpull] at hgn
    exact mem_map_of_mem L.subtype (hlocal hgn)
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_isPGroup_of_normalizer_eq
    twoSubgroup twoSubgroup_isPGroup hself
  intro S
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model P S
  have hmap : twoSubgroup.map (MulAut.conj g).toMonoidHom = S.toSubgroup := by
    rw [← hP]
    exact congrArg Sylow.toSubgroup hg
  change normalizer (S.toSubgroup : Set Model) ≤ S.toSubgroup
  rw [← hmap, ← Subgroup.map_equiv_normalizer_eq, hself]

end Janko4.LocalStructure.SymmetricLinear
