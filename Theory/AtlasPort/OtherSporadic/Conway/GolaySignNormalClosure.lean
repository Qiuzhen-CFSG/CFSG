/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/GolaySignNormalClosure.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.NormalGenerationElement
public import Theory.AtlasPort.OtherSporadic.Conway.DerivedCrossPrimitivity
public import Theory.AtlasPort.OtherSporadic.Conway.MonomialPerfectness
public import Theory.AtlasPort.OtherSporadic.GroupTheory.NormalSimpleImage

/-!
Normal generation by Golay signs and perfectness of the Leech isometry group.
An explicit conjugate has nonidentity Mathieu image, forcing the full monomial subgroup and then the whole group.

Source: Gerald Höhn, `Atlas/Conway/GolaySignNormalClosure.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def golaySignSubgroup : Subgroup LeechIsometryGroup := signEmbedding.range

def golaySignNormalClosure : Subgroup LeechIsometryGroup :=
  Subgroup.normalClosure (golaySignSubgroup : Set LeechIsometryGroup)

instance golaySignNormalClosure_normal : golaySignNormalClosure.Normal :=
  Subgroup.normalClosure_normal

theorem golaySignSubgroup_le_normalClosure : golaySignSubgroup ≤ golaySignNormalClosure :=
  Subgroup.subset_normalClosure

theorem normalGenerationConjugate_mem_normalClosure :
    normalGenerationConjugate ∈ golaySignNormalClosure := by
  exact (inferInstance : golaySignNormalClosure.Normal).conj_mem _
    (golaySignSubgroup_le_normalClosure ⟨Multiplicative.ofAdd normalGenerationCode,rfl⟩) zeta

theorem monomial_le_signNormalClosure : monomialSubgroup ≤ golaySignNormalClosure := by
  let L := golaySignNormalClosure.comap monomialEmbedding
  let f : GolayMonomialGroup →* Mathieu24CodeModel := SemidirectProduct.rightHom
  have hk : f.ker ≤ L := by
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
    rintro x ⟨c,rfl⟩
    change monomialEmbedding (SemidirectProduct.inl c) ∈ golaySignNormalClosure
    have hi : monomialEmbedding (SemidirectProduct.inl c) = signEmbedding c :=
      congrArg (fun f : Multiplicative golay →* LeechIsometryGroup => f c) monomial_inl
    rw [hi]
    exact golaySignSubgroup_le_normalClosure ⟨c,rfl⟩
  have ht : normalGenerationMonomial ∈ L := by
    change monomialEmbedding normalGenerationMonomial ∈ golaySignNormalClosure
    rw [normalGenerationMonomial_image]
    exact normalGenerationConjugate_mem_normalClosure
  let := mathieu24_simple
  have he : L = ⊤ := Atlas.GroupTheory.normal_eq_top_of_simple_image f
    SemidirectProduct.rightHom_surjective L hk normalGenerationMonomial ht
    normalGenerationMonomial_permutation_ne_one
  rintro g ⟨m,rfl⟩
  exact (show m ∈ L from he ▸ Subgroup.mem_top m)

theorem golaySign_normalClosure_eq_full : golaySignNormalClosure = ⊤ := by
  apply strict_overgroup_eq_full
  refine lt_of_le_of_ne monomial_le_signNormalClosure ?_
  intro he
  have hn : monomialSubgroup.Normal := he.symm ▸ golaySignNormalClosure_normal
  exact monomial_not_normal hn

theorem golaySignSubgroup_le_monomial : golaySignSubgroup ≤ monomialSubgroup := by
  rintro g ⟨c,rfl⟩
  exact ⟨SemidirectProduct.inl c,congrArg
    (fun f : Multiplicative golay →* LeechIsometryGroup => f c) monomial_inl⟩

theorem leechIsometryGroup_perfect : Group.IsPerfect LeechIsometryGroup := by
  let := monomialSubgroup_perfect
  have hN : monomialSubgroup ≤ commutator LeechIsometryGroup := by
    have he : (commutator monomialSubgroup).map monomialSubgroup.subtype = monomialSubgroup := by
      rw [Group.IsPerfect.commutator_eq_top,← MonoidHom.range_eq_map,Subgroup.range_subtype]
    rw [← he]
    exact (map_commutator_eq _ monomialSubgroup.subtype).le.trans
      (Subgroup.commutator_mono le_top le_top)
  have hK : golaySignNormalClosure ≤ commutator LeechIsometryGroup :=
    Subgroup.normalClosure_le_normal (golaySignSubgroup_le_monomial.trans hN)
  constructor
  exact top_unique (golaySign_normalClosure_eq_full ▸ hK)

theorem leechCentralQuotient_perfect : Group.IsPerfect LeechCentralQuotient := by
  let := leechIsometryGroup_perfect
  exact Group.IsPerfect.ofSurjective leechCentralProjection_surjective

end Atlas.Conway
