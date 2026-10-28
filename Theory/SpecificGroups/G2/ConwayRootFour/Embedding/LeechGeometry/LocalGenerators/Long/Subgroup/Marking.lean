module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.ScalarFour
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups

/-!
# Transporting a tetrahedral scalar marking

The normal Klein four group of an embedded A₄ is a Sylow two-subgroup of A₅.
Its normalizer is that A₄, so Sylow conjugacy conjugates any two such images.
Mapping the conjugator through the genuine scalar embedding identifies the
image with the literal `I`; no evaluation of the noncomputable five-point
icosian equivalence is used. `Long.Subgroup` applies this to lattice generators.

Source: Aschbacher, *Sporadic Groups* (1994), Section 48, p.269, and Lemma 49.5,
p.283. This is marking transport, not the construction of K₁.
-/

@[expose] public section
open Subgroup
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
open scoped Pointwise
private abbrev A4 := alternatingGroup fourPoints
private abbrev A5 := alternatingGroup (Fin 5)

private noncomputable def imageSylow (j : A4 →* A5) (hj : Function.Injective j) :
    Sylow 2 A5 := Sylow.ofCard ((alternatingGroup.kleinFour fourPoints).map j) (by
  rw [Subgroup.card_map_of_injective hj,
    alternatingGroup.kleinFour_card_of_card_eq_four fourPoints_card,
    nat_card_alternatingGroup]
  simp only [Nat.card_fin]
  decide +kernel)

private theorem range_eq_normalizer (j : A4 →* A5) (hj : Function.Injective j) :
    j.range = normalizer (imageSylow j hj : Set A5) := by
  let _ := alternatingGroup.normal_kleinFour fourPoints_card
  have hle : j.range ≤ normalizer (imageSylow j hj : Set A5) := by
    rw [← Sylow.coe_coe, imageSylow, Sylow.coe_ofCard]
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using
      (alternatingGroup.kleinFour fourPoints).le_normalizer_map j
  apply Subgroup.eq_of_le_of_card_ge hle
  have hc : Nat.card j.range = 12 :=
    (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans
      (alternatingGroup.card_of_card_eq_four fourPoints_card)
  rw [hc]
  obtain ⟨i, hi⟩ :=
    Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer
      (imageSylow j hj)
  rw [hi]
  have hc' : ∀ i : Fin 5, Nat.card (MulAction.stabilizer A5 i) = 12 := by
    intro i
    rw [Nat.card_eq_fintype_card]
    revert i
    decide +kernel
  exact (hc' i).le

/-- Any two tetrahedral embeddings in the fixed scalar A₅ have conjugate images. -/
theorem tetrahedral_ranges_conjugate (j k : alternatingGroup fourPoints →* alternatingGroup (Fin 5))
    (hj : Function.Injective j) (hk : Function.Injective k) :
    ∃ g : alternatingGroup (Fin 5), j.range.map (MulAut.conj g).toMonoidHom = k.range := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A5 (imageSylow j hj) (imageSylow k hk)
  have hP : (imageSylow j hj : Subgroup A5).map (MulAut.conj g).toMonoidHom =
      (imageSylow k hk : Subgroup A5) := by
    have h := congrArg (fun P : Sylow 2 A5 => (P : Subgroup A5)) hg
    rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  refine ⟨g, ?_⟩
  rw [range_eq_normalizer j hj, range_eq_normalizer k hk]
  have hn := Subgroup.map_equiv_normalizer_eq
    (imageSylow j hj : Subgroup A5) (MulAut.conj g)
  exact hn.trans (congrArg (fun P : Subgroup A5 => normalizer (P : Set A5)) hP)

/-- Transport to the literal `I`, without evaluating the noncomputable
five-point marking of the icosian scalars. -/
theorem scalar_tetrahedral_conjugate
    (j : alternatingGroup fourPoints →* alternatingGroup (Fin 5)) (hj : Function.Injective j) :
    ∃ g : Atlas.Conway.LeechCentralQuotient,
      (scalarFive.comp j).range.map (MulAut.conj g).toMonoidHom = I := by
  obtain ⟨g, hg⟩ := tetrahedral_ranges_conjugate j
    (alternatingGroup.ofSubtype fourPoints) hj alternatingGroup.ofSubtype_injective
  refine ⟨scalarFive g, ?_⟩
  have he : (MulAut.conj (scalarFive g)).toMonoidHom.comp scalarFive =
      scalarFive.comp (MulAut.conj g).toMonoidHom := by
    ext a
    simp
  rw [MonoidHom.range_comp, Subgroup.map_map, he, ← Subgroup.map_map, hg]
  exact (MonoidHom.range_comp scalarFive (alternatingGroup.ofSubtype fourPoints)).symm
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
