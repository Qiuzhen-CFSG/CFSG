module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.Certificates
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondQuotient

/-!
# Recognizing the second Tits parabolic from its marked collection equations

The literal Sylow subgroup and a proposed reflection give nine generators.
The checked three-coset table identifies their graph with the actual second
parabolic. Equal orders make the second projection injective as well. The
result preserves every element of the specified Sylow, not just its order.

This is a conditional presentation theorem: construction of a reflection
satisfying the table remains a separate obligation. It is used for the cubic
vertex in Aschbacher--Smith F.1.12 and 14.2.20--21, pp.263 and 988--989.
The generator and right-coset conventions are Parrott (1972), §5, p.683.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.SecondRecognition
open Subgroup AmalgamRigidity.SecondExtension RelativeSecondBlockLayers

/-- The original second core, regarded as a subgroup of the common Sylow. -/
def coreInSylow : Subgroup S :=
  (pCore 2 second).comap (inclusion sylow_le_second)

/-- The positive generator at zero is an unused dummy. -/
def positive (a : Fin 9) : S :=
  if h : a = 0 then 1 else
    ⟨(gen a).val, by
      change SecondOrder.generator a ∈ S
      rw [S, atlas1600SylowTwoSubgroup_eq]
      apply Subgroup.subset_closure
      fin_cases a <;> simp_all [SecondOrder.generator, SecondOrder.generatorIndex]⟩

theorem inclusion_positive (a : Fin 9) (ha : a ≠ 0) :
    inclusion sylow_le_second (positive a) = gen a := by
  simp only [positive, dif_neg ha]
  rfl

/-- Use the actual Sylow embedding for the eight positive generators. -/
def generators {P : Type*} [Group P] (j : S →* P) (r : P) (a : Fin 9) : P :=
  if a = 0 then r else j (positive a)

private theorem positive_relations : SylowRelations positive := by
  apply SylowRelations.of_injective (inclusion sylow_le_second)
    (inclusion_injective sylow_le_second)
  constructor
  · simpa [inclusion_positive] using gen_sylowRelations.power_1
  · simpa [inclusion_positive] using gen_sylowRelations.power_2
  · simpa [inclusion_positive] using gen_sylowRelations.power_3
  · simpa [inclusion_positive] using gen_sylowRelations.power_4
  · simpa [inclusion_positive] using gen_sylowRelations.power_5
  · simpa [inclusion_positive] using gen_sylowRelations.power_6
  · simpa [inclusion_positive] using gen_sylowRelations.power_7
  · simpa [inclusion_positive] using gen_sylowRelations.power_8
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_2_1
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_3_1
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_3_2
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_4_1
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_4_2
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_4_3
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_5_1
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_5_2
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_5_3
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_5_4
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_6_1
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_6_2
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_6_3
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_6_4
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_6_5
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_7_1
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_7_2
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_7_3
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_7_4
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_7_5
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_7_6
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_8_1
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_8_2
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_8_3
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_8_4
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_8_5
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_8_6
  · simpa [inclusion_positive] using gen_sylowRelations.conjugate_8_7

/-- All positive collection equations follow from the original Sylow map. -/
theorem generators_sylowRelations {P : Type*} [Group P] (j : S →* P) (r : P) :
    SylowRelations (generators j r) := by
  constructor
  · simpa [generators] using congrArg j positive_relations.power_1
  · simpa [generators] using congrArg j positive_relations.power_2
  · simpa [generators] using congrArg j positive_relations.power_3
  · simpa [generators] using congrArg j positive_relations.power_4
  · simpa [generators] using congrArg j positive_relations.power_5
  · simpa [generators] using congrArg j positive_relations.power_6
  · simpa [generators] using congrArg j positive_relations.power_7
  · simpa [generators] using congrArg j positive_relations.power_8
  · simpa [generators] using congrArg j positive_relations.conjugate_2_1
  · simpa [generators] using congrArg j positive_relations.conjugate_3_1
  · simpa [generators] using congrArg j positive_relations.conjugate_3_2
  · simpa [generators] using congrArg j positive_relations.conjugate_4_1
  · simpa [generators] using congrArg j positive_relations.conjugate_4_2
  · simpa [generators] using congrArg j positive_relations.conjugate_4_3
  · simpa [generators] using congrArg j positive_relations.conjugate_5_1
  · simpa [generators] using congrArg j positive_relations.conjugate_5_2
  · simpa [generators] using congrArg j positive_relations.conjugate_5_3
  · simpa [generators] using congrArg j positive_relations.conjugate_5_4
  · simpa [generators] using congrArg j positive_relations.conjugate_6_1
  · simpa [generators] using congrArg j positive_relations.conjugate_6_2
  · simpa [generators] using congrArg j positive_relations.conjugate_6_3
  · simpa [generators] using congrArg j positive_relations.conjugate_6_4
  · simpa [generators] using congrArg j positive_relations.conjugate_6_5
  · simpa [generators] using congrArg j positive_relations.conjugate_7_1
  · simpa [generators] using congrArg j positive_relations.conjugate_7_2
  · simpa [generators] using congrArg j positive_relations.conjugate_7_3
  · simpa [generators] using congrArg j positive_relations.conjugate_7_4
  · simpa [generators] using congrArg j positive_relations.conjugate_7_5
  · simpa [generators] using congrArg j positive_relations.conjugate_7_6
  · simpa [generators] using congrArg j positive_relations.conjugate_8_1
  · simpa [generators] using congrArg j positive_relations.conjugate_8_2
  · simpa [generators] using congrArg j positive_relations.conjugate_8_3
  · simpa [generators] using congrArg j positive_relations.conjugate_8_4
  · simpa [generators] using congrArg j positive_relations.conjugate_8_5
  · simpa [generators] using congrArg j positive_relations.conjugate_8_6
  · simpa [generators] using congrArg j positive_relations.conjugate_8_7

/-- The literal three-coset equations produce a marked group isomorphism. -/
theorem exists_equiv_of_collection {P : Type*} [Group P] [Finite P]
    (h : Fin 9 → P) (hs : SylowRelations h) (hc : CosetRelations h)
    (hg : closure (Set.range h) = ⊤) (hcard : Nat.card P = 6144) :
    ∃ e : second ≃* P, ∀ i, e (gen i) = h i := by
  let k : Fin 9 → second × P := fun i => (gen i, h i)
  let K := closure (Set.range k)
  let q₁ : K →* second := (MonoidHom.fst second P).comp K.subtype
  let q₂ : K →* P := (MonoidHom.snd second P).comp K.subtype
  have hq₁ : Function.Surjective q₁ := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← gen_generates]
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨k i, subset_closure ⟨i, rfl⟩⟩, rfl⟩
  have hq₂ : Function.Surjective q₂ := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← hg]
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨k i, subset_closure ⟨i, rfl⟩⟩, rfl⟩
  have hk₁ : Function.Injective q₁ := by
    intro x y hxy
    obtain ⟨p, hp⟩ := normalForm_surjective k (gen_sylowRelations.prod hs)
      (gen_cosetRelations.prod hc) x.property
    obtain ⟨q, hq⟩ := normalForm_surjective k (gen_sylowRelations.prod hs)
      (gen_cosetRelations.prod hc) y.property
    have he : p = q := secondNormalForm_bijective.injective (by
      change x.val.1 = y.val.1 at hxy
      rw [← hp, ← hq] at hxy
      change word gen p.1 * rep gen p.2 = word gen q.1 * rep gen q.2 at hxy
      simpa only [normalForm_gen] using hxy)
    exact Subtype.ext (hp.symm.trans (he ▸ hq))
  let e₁ : K ≃* second := MulEquiv.ofBijective q₁ ⟨hk₁, hq₁⟩
  let f : second →* P := q₂.comp e₁.symm.toMonoidHom
  have hf : Function.Surjective f := hq₂.comp e₁.symm.surjective
  let e : second ≃* P := MulEquiv.ofBijective f
    (hf.bijective_of_nat_card_le (by rw [hcard, ExceptionalParabolics.second_card]))
  refine ⟨e, fun i => ?_⟩
  have hi : e₁ ⟨k i, subset_closure ⟨i, rfl⟩⟩ = gen i := rfl
  change q₂ (e₁.symm (gen i)) = h i
  rw [← hi, e₁.symm_apply_apply]
  rfl

private theorem word_positive (n : Fin 2048) :
    word positive n = atlas1600SylowTwoEquiv n := by
  apply (inclusion_injective sylow_le_second)
  rw [map_word]
  have he : word ((inclusion sylow_le_second) ∘ positive) n = word gen n := by
    simp [word, inclusion_positive]
  rw [he]
  apply Subtype.ext
  exact (word_gen_val n).trans (atlas1600SylowTwoEquiv_apply n).symm

/-- Recognition preserves the entire original Sylow embedding. -/
theorem exists_marked_equiv {P : Type*} [Group P] [Finite P]
    (j : S →* P) (r : P) (hc : CosetRelations (generators j r))
    (hg : closure (Set.range (generators j r)) = ⊤) (hcard : Nat.card P = 6144) :
    ∃ e : second ≃* P,
      (∀ s : S, e (inclusion sylow_le_second s) = j s) ∧ e (gen 0) = r := by
  obtain ⟨e, he⟩ := exists_equiv_of_collection (generators j r)
    (generators_sylowRelations j r) hc hg hcard
  refine ⟨e, ?_, by simpa [generators] using he 0⟩
  intro s
  obtain ⟨n, rfl⟩ := atlas1600SylowTwoEquiv.surjective s
  rw [← word_positive, map_word, map_word]
  simp [word, inclusion_positive, he, generators]

/-- A reflection outside an index-three marked Sylow generates the whole vertex. -/
theorem generators_generate {P : Type*} [Group P] [Finite P]
    (j : S →* P) (r : P) (hi : j.range.index = 3) (hr : r ∉ j.range) :
    closure (Set.range (generators j r)) = ⊤ := by
  let L := closure (Set.range (generators j r))
  have hj : j.range ≤ L := by
    rintro _ ⟨s,rfl⟩
    obtain ⟨n,rfl⟩ := atlas1600SylowTwoEquiv.surjective s
    rw [← word_positive, map_word]
    apply word_mem_of
    intro a ha
    change j (positive a) ∈ L
    have he : j (positive a) = generators j r a := by simp [generators,ha]
    rw [he]
    exact Subgroup.subset_closure ⟨a,rfl⟩
  have hrL : r ∈ L := by
    have he : generators j r 0 = r := by simp [generators]
    exact he ▸ (Subgroup.subset_closure ⟨0,rfl⟩)
  have hd : L.index ∣ 3 := hi ▸ index_dvd_of_le hj
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact index_eq_one.mp h1
  · have hmul := relIndex_mul_index hj
    rw [hi,h3] at hmul
    have hrel : j.range.relIndex L = 1 := by omega
    exact (hr (relIndex_eq_one.mp hrel hrL)).elim

end Tits.ExceptionalParabolics.SecondRecognition
