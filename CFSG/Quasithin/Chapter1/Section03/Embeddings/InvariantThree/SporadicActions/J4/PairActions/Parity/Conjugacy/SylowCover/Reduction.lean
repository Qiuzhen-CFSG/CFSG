module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.SylowCandidate
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.Conjugacy

/-!+# Actual embeddings in the J₄ Sylow-overgroup problem

Abstract isomorphism types do not determine conjugacy of subgroups. We separate
the remaining conjugacy assertion for maximal embeddings of the three literal
ATLAS carriers from exhaustion by those isomorphism types. Neither assertion
is proved by introducing the list.

The certified max2 word conjugation does suffice to put every conjugate of
the literal max2 subgroup inside a conjugate of C_Model(a). Full generation of
that centralizer is unnecessary. Independently, the certified subgroup of
order 2²¹ shows that every ambient Sylow overgroup has order divisible by 2²¹.
Thus excluding smaller two-parts needs no exact order calculation for J₄.

Source: Kleidman–Wilson, *The maximal subgroups of J₄*, Proc. London Math.
Soc. 56 (1988), 484–510; the literal carriers are documented in their imported
modules. The application in Aschbacher–Smith, printed p.511/PDF p.528 of
`refs/quasithin.pdf`, cites Aschbacher's Sylow-overgroup analysis (1986).
-/

public section

open Subgroup Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

/-- The three actual matrix-word subgroups; membership asserts no exhaustion. -/
@[expose] def listedSubgroups : Set (Subgroup Janko4.Model) :=
  {Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four,
    sourceSubgroup, max4Subgroup}

/-- The remaining embedding comparison, restricted to maximal Sylow overgroups.
The isomorphism is an explicit input; constructing it is a separate exhaustion
problem. This definition does not assert that such embeddings are conjugate. -/
@[expose] def ListedMaximalEmbeddingConjugacy : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (M L : Subgroup Janko4.Model),
    IsCoatom M → S.toSubgroup ≤ M → L ∈ listedSubgroups → Nonempty (M ≃* L) →
      ∃ g : Janko4.Model, M = L.map (MulAut.conj g).toMonoidHom

/-- The local order certificate supplies a lower bound on every ambient Sylow
two-part without assuming that the specified two-subgroup is itself Sylow. -/
theorem two_pow_twentyOne_dvd_sylow_card (S : Sylow 2 Janko4.Model) :
    2 ^ 21 ∣ Nat.card S := by
  apply S.pow_dvd_card_of_pow_dvd_card
  rw [← Janko4.OuterReduction.OddIndex.twoSubgroup_card]
  exact Janko4.OuterReduction.OddIndex.twoSubgroup.card_subgroup_dvd_card

/-- Every actual overgroup of an ambient Sylow has this certified two-part. -/
theorem two_pow_twentyOne_dvd_card_of_sylow_le (S : Sylow 2 Janko4.Model)
    (H : Subgroup Janko4.Model) (hSH : S.toSubgroup ≤ H) :
    2 ^ 21 ∣ Nat.card H :=
  (two_pow_twentyOne_dvd_sylow_card S).trans (card_dvd_of_le hSH)

/-- A subgroup with smaller two-part, in any conjugate position, cannot
contain an ambient Sylow subgroup. A source-table order alone is not a premise:
the bound here concerns the actual subgroup's cardinality. -/
theorem not_sylow_le_conjugate_of_two_part (S : Sylow 2 Janko4.Model)
    (H : Subgroup Janko4.Model) (hH : ¬ 2 ^ 21 ∣ Nat.card H) (g : Janko4.Model) :
    ¬ S.toSubgroup ≤ H.map (MulAut.conj g).toMonoidHom := by
  intro hSH
  apply hH
  have hd := two_pow_twentyOne_dvd_card_of_sylow_le S _ hSH
  rwa [card_map_of_injective (K := H) (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective] at hd

/-- The proved conjugation is by h⁻¹, hence the original max2 carrier lies in
h C_Model(a) h⁻¹. This uses only the certified inclusion in the centralizer. -/
theorem sourceSubgroup_le_conjugate_centralizer :
    sourceSubgroup ≤ (centralizer ({Janko4.a} : Set Janko4.Model)).map
      (MulAut.conj h).toMonoidHom := by
  have hc : sourceSubgroup.map (MulAut.conj h⁻¹).toMonoidHom ≤
      centralizer ({Janko4.a} : Set Janko4.Model) := by
    rw [sourceSubgroup_map_conj, ← centralizerToModel_range]
    exact map_le_range _ _
  have hm := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hc
  rw [map_map] at hm
  have he : (MulAut.conj h).toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom =
      MonoidHom.id Janko4.Model := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  simpa only [he, map_id] using hm

/-- Transport the actual max2 inclusion with the g H g⁻¹ convention. -/
theorem sourceSubgroup_conjugate_le_centralizer (g : Janko4.Model) :
    sourceSubgroup.map (MulAut.conj g).toMonoidHom ≤
      (centralizer ({Janko4.a} : Set Janko4.Model)).map
        (MulAut.conj (g * h)).toMonoidHom := by
  have hm := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
    sourceSubgroup_le_conjugate_centralizer
  rw [map_map] at hm
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (g * h)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rwa [he] at hm

/-- Finiteness enlarges any proper Sylow overgroup to a maximal one. -/
theorem exists_maximal_sylow_overgroup (S : Sylow 2 Janko4.Model)
    (H : Subgroup Janko4.Model) (hSH : S.toSubgroup ≤ H) (hH : H ≠ ⊤) :
    ∃ M : Subgroup Janko4.Model, IsCoatom M ∧ H ≤ M ∧ S.toSubgroup ≤ M := by
  obtain ⟨M, hM, hHM⟩ := (eq_top_or_exists_le_coatom H).resolve_left hH
  exact ⟨M, hM, hHM, hSH.trans hHM⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
