module

public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding.Words
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding.Relations.Comparison
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding.Relations.PartI
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding.Relations.PartII
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding.Relations.PartIII
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding.Relations.PartIV
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding.Relations.PartV
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding.Relations.PartVI
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding.Relations.PartVII
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding.Relations.PartVIII

/-!+# Parrott's relations in the Rudvalis point stabilizer

The ten elements of `assignment` satisfy all 37 relators from Parrott (1972),
§5, p.683, with the original product order and commutator convention. The
certificate first identifies each published word with an explicit permutation
of the 4060 points, then checks each source relator in those permutations.
Injectivity of the carrier's inclusion in the symmetric group transports the
result to the actual Rudvalis model. Every finite comparison is kernel checked.

This supplies the presentation input for the Tits subgroup of the point
stabilizer in GLS3 Table 5.3r, printed p.279. The index and identification with
the Tits group are separate assembly results. Source transcription:
`refs/original/n-group-global/parrott-tits-presentation.md`. The word witnesses
and their ATLAS provenance are documented in `Words.lean`.
-/

namespace Rudvalis.OuterStabilizer.TitsEmbedding
open RelationCertificate

private theorem permutation_relations : Tits.SatisfiesParrottRelations permutation := by
  intro i
  cases i
  · exact relation_i_r1
  · exact relation_i_r8
  · exact relation_i_s1
  · exact relation_i_s2
  · exact relation_i_s4
  · exact relation_i_s6
  · exact relation_i_s8
  · exact relation_i_s3
  · exact relation_i_s5
  · exact relation_i_s7
  · exact relation_ii_s1_s2
  · exact relation_ii_s1_s3
  · exact relation_ii_s1_s5
  · exact relation_iii_s1_s6
  · exact relation_iii_s1_s7
  · exact relation_iii_s1_s8
  · exact relation_iv_s2_s4
  · exact relation_iv_s2_s6
  · exact relation_iv_s2_s8
  · exact relation_iv_s7_s2
  · exact relation_v_s7_s4
  · exact relation_v_s3_s5
  · exact relation_v_s5_s4
  · exact relation_vi_r1_r8
  · exact relation_vi_s1_r1
  · exact relation_vi_r8_s8
  · exact relation_vii_s2
  · exact relation_vii_s4
  · exact relation_vii_s5
  · exact relation_vii_s3
  · exact relation_vii_r3
  · exact relation_viii_s2
  · exact relation_viii_s4
  · exact relation_viii_s1
  · exact relation_viii_s7
  · exact relation_viii_s3
  · exact relation_viii_r3

/-- The ten published Rudvalis stabilizer words satisfy all 37 of Parrott's
original relations, with no additional hypotheses. -/
public theorem assignment_relations : Tits.SatisfiesParrottRelations assignment := by
  let inclusion : Model →* Equiv.Perm (Fin 4060) := modelSubgroup.subtype
  have hcomp : inclusion.comp (FreeGroup.lift assignment) = FreeGroup.lift permutation := by
    apply FreeGroup.ext_hom
    intro a
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact (permutation_eq a).symm
  intro i
  apply Subtype.ext
  change (inclusion.comp (FreeGroup.lift assignment)) (Tits.parrottRelator i) = 1
  rw [hcomp]
  exact permutation_relations i

end Rudvalis.OuterStabilizer.TitsEmbedding
