module

public import Theory.Mathieu.M24.Properties.Transitivity
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryKernel.Translations
public import Theory.GroupAction.AutomorphismNormalizer

/-!
# The permutation normalizer of the concrete M24

The certified M23 heptad translations extend to M24, fixing an octad
pointwise and acting transitively on its sixteen-point complement. Thus
that octad is their only invariant eight-set. Five-transitivity and the
Steiner property recover every octad from this local observation. A
permutation normalizing M24 must therefore preserve the Witt design,
so it belongs to M24.

This proves self-normalization in Sym(24). Reconstruction of arbitrary
abstract automorphisms from this permutation action is a separate obligation.
It does not follow just from defining M24 as the design automorphism group.

Source: GLS3, Table 5.3e and Note 1; Aschbacher, *Sporadic Groups*,
Sections 18–19, for the Witt design and its binary translation subgroup.
The proof uses the existing concrete carrier and requires no model transport.
-/

open scoped Pointwise
namespace Sporadic.Mathieu.M24OuterRestriction

private theorem coe_finset_smul (g : M24) (B : Finset (Fin 24)) :
    g • B = g.val • B := by
  rfl

private def octad : Finset (Fin 24) := {0, 1, 2, 3, 4, 5, 11, 17}
private def five : Finset (Fin 24) := {1, 2, 3, 4, 5}

private theorem octad_card : octad.card = 8 := by decide +kernel
private theorem five_card : five.card = 5 := by decide +kernel
private theorem five_subset : five ⊆ octad := by decide +kernel
private theorem octad_mem : octad ∈ m24Blocks := by
  have he : octad = m24BlockAt 0 := by decide +kernel
  rw [he, m24Blocks]
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

private theorem octad_eq_augmented : octad = m23AugmentedBlock M23Geometry.omega := by
  decide +kernel

private noncomputable def translation (v : Fin 4 → ZMod 2) : M24 :=
  ⟨m23ExtendHom ⟨M23Geometry.heptadBinaryPermutation v,
      M23Geometry.heptadBinaryPermutation_mem v⟩,
    m23Extend_mem_M24 _⟩

private theorem translation_fixes (v : Fin 4 → ZMod 2) (x : Fin 24)
    (hx : x ∈ octad) : translation v • x = x := by
  rw [octad_eq_augmented, m23AugmentedBlock_eq_insert_map, Finset.mem_insert] at hx
  change m23ExtendHom _ x = x
  rcases hx with rfl | hx
  · exact m23ExtendHom_apply_24 _
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    rw [m23ExtendHom_apply_embedded]
    exact congrArg m23PointEmbedding (M23Geometry.heptadBinaryPermutation_fix v i hi)

private theorem complement_lift (x : Fin 24) (hx : x ∉ octad) :
    ∃ i : Fin 23, i ∉ M23Geometry.omega ∧ m23PointEmbedding i = x := by
  have hzero : x ≠ (24 : Fin 24) := by
    intro he
    subst x
    exact hx (by decide +kernel)
  obtain ⟨i, hi⟩ := m23PointEquiv.surjective ⟨x, hzero⟩
  have he : m23PointEmbedding i = x := congrArg Subtype.val hi
  refine ⟨i, ?_, he⟩
  intro himem
  apply hx
  rw [octad_eq_augmented, m23AugmentedBlock_eq_insert_map, ← he]
  exact Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨i, himem, rfl⟩)

private theorem translations_transitive (x y : Fin 24) (hx : x ∉ octad) (hy : y ∉ octad) :
    ∃ v : Fin 4 → ZMod 2, translation v • x = y := by
  obtain ⟨i, hi, rfl⟩ := complement_lift x hx
  obtain ⟨j, hj, rfl⟩ := complement_lift y hy
  obtain ⟨v, rfl⟩ := M23Geometry.heptadBinaryPoint_surjective i hi
  obtain ⟨w, rfl⟩ := M23Geometry.heptadBinaryPoint_surjective j hj
  refine ⟨w - v, ?_⟩
  change m23ExtendHom _ _ = _
  rw [m23ExtendHom_apply_embedded]
  change m23PointEmbedding (M23Geometry.heptadBinaryPermutation (w - v)
    (M23Geometry.heptadBinaryPoint v)) = _
  rw [M23Geometry.heptadBinaryPermutation_translate, sub_add_cancel]

private theorem invariant_eight_eq_octad (B : Finset (Fin 24)) (hB : B.card = 8)
    (hinv : ∀ v : Fin 4 → ZMod 2, translation v • B = B) : B = octad := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    by_contra hxo
    have hc : Finset.univ \ octad ⊆ B := by
      intro y hy
      obtain ⟨v, hv⟩ := translations_transitive x y hxo (Finset.mem_sdiff.mp hy).2
      rw [← hv, ← hinv v]
      exact Finset.smul_mem_smul_finset hx
    have hn := Finset.card_le_card hc
    have ho : (Finset.univ \ octad).card = 16 := by decide +kernel
    omega
  · rw [octad_card, hB]

private theorem smul_mem_blocks (g : M24) {B : Finset (Fin 24)} (hB : B ∈ m24Blocks) :
    g • B ∈ m24Blocks := by
  have hg := (mem_M24_iff g.val).mp g.property
  have hm := Set.smul_mem_smul_set (a := g.val) hB
  rw [hg] at hm
  exact hm

private theorem blocks_eq_of_five {S B C : Finset (Fin 24)}
    (hS : S.card = 5) (hB : B ∈ m24Blocks) (hC : C ∈ m24Blocks)
    (hSB : S ⊆ B) (hSC : S ⊆ C) : B = C := by
  obtain ⟨D, hD⟩ := Finset.card_eq_one.mp (m24Blocks_unique_block S hS)
  have hb : B ∈ m24Blocks.filter (fun B => S ⊆ B) := Finset.mem_filter.mpr ⟨hB, hSB⟩
  have hc : C ∈ m24Blocks.filter (fun B => S ⊆ B) := Finset.mem_filter.mpr ⟨hC, hSC⟩
  rw [hD, Finset.mem_singleton] at hb hc
  exact hb.trans hc.symm

private theorem block_fixed_of_five (g : M24) {S B : Finset (Fin 24)}
    (hS : S.card = 5) (hB : B ∈ m24Blocks) (hSB : S ⊆ B)
    (hfix : ∀ x ∈ S, g • x = x) : g • B = B := by
  apply blocks_eq_of_five hS (smul_mem_blocks g hB) hB ?_ hSB
  intro x hx
  rw [← hfix x hx]
  exact Finset.smul_mem_smul_finset (hSB hx)

private theorem five_transitive (S T : Finset (Fin 24)) (hS : S.card = 5)
    (hT : T.card = 5) : ∃ g : M24, g • S = T := by
  let eS := (Finset.equivFinOfCardEq hS).symm
  let eT := (Finset.equivFinOfCardEq hT).symm
  let x : Fin 5 ↪ Fin 24 := eS.toEmbedding.trans (Function.Embedding.subtype _)
  let y : Fin 5 ↪ Fin 24 := eT.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨g, hg⟩ := m24_isFivePretransitive.exists_smul_eq x y
  refine ⟨g, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_smul_finset.mp hb
    obtain ⟨i, hi⟩ := eS.surjective ⟨a, ha⟩
    have hgi : g • x i = y i := congrArg (fun z : Fin 5 ↪ Fin 24 => z i) hg
    have hxi : x i = a := congrArg Subtype.val hi
    rw [← hxi, hgi]
    exact (eT i).property
  · simp only [Finset.card_smul_finset, hS, hT, le_refl]

private theorem octads_transitive {B : Finset (Fin 24)} (hB : B ∈ m24Blocks) :
    ∃ g : M24, g • octad = B := by
  obtain ⟨S, hSB, hS⟩ := Finset.exists_subset_card_eq
    (show 5 ≤ B.card by rw [m24Blocks_card B hB]; omega)
  obtain ⟨g, hg⟩ := five_transitive five S five_card hS
  refine ⟨g, blocks_eq_of_five hS (smul_mem_blocks g octad_mem) hB ?_ hSB⟩
  intro x hx
  rw [← hg] at hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_smul_finset.mp hx
  exact Finset.smul_mem_smul_finset (five_subset ha)

private theorem normalizer_image_octad (σ : Equiv.Perm (Fin 24))
    (hσ : σ ∈ Subgroup.normalizer (M24 : Set (Equiv.Perm (Fin 24)))) :
    σ • octad ∈ m24Blocks := by
  obtain ⟨g, hg⟩ := five_transitive five (σ • five) five_card
    (by simpa only [Finset.card_smul_finset] using five_card)
  let τ : Equiv.Perm (Fin 24) := g.val⁻¹ * σ
  have hτ : τ ∈ Subgroup.normalizer (M24 : Set (Equiv.Perm (Fin 24))) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer g.property)) hσ
  have hτfive : τ • five = five := by
    change (g.val⁻¹ * σ) • five = five
    rw [mul_smul, ← hg]
    exact inv_smul_smul g.val five
  have hinv (v : Fin 4 → ZMod 2) : translation v • (τ • octad) = τ • octad := by
    let u : M24 := ⟨τ⁻¹ * (translation v).val * τ,
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hτ) _).mp
        (translation v).property⟩
    have hufix (x : Fin 24) (hx : x ∈ five) : u • x = x := by
      have hτx : τ x ∈ five := by
        rw [← hτfive]
        exact Finset.smul_mem_smul_finset hx
      change τ⁻¹ ((translation v).val (τ x)) = x
      rw [show (translation v).val (τ x) = τ x from translation_fixes v _ (five_subset hτx)]
      exact τ.symm_apply_apply x
    have hu := block_fixed_of_five u five_card octad_mem five_subset hufix
    have he := congrArg (fun B : Finset (Fin 24) => τ • B) hu
    rw [coe_finset_smul]
    simpa only [coe_finset_smul, u, mul_smul, smul_inv_smul] using he
  have he := invariant_eight_eq_octad (τ • octad)
    (by simpa only [Finset.card_smul_finset] using octad_card) hinv
  have hgo : σ • octad = g • octad := by
    have hh := congrArg (fun B : Finset (Fin 24) => g.val • B) he
    rw [coe_finset_smul]
    simpa only [τ, mul_smul, smul_inv_smul] using hh
  rw [hgo]
  exact smul_mem_blocks g octad_mem

/-- The full Witt-design group is self-normalizing in its natural symmetric group. -/
public theorem normalizer_eq : Subgroup.normalizer (M24 : Set (Equiv.Perm (Fin 24))) = M24 := by
  apply le_antisymm ?_ Subgroup.le_normalizer
  intro σ hσ
  apply (mem_M24_iff σ).mpr
  apply Set.Subset.antisymm
  · rintro B ⟨C, hC, rfl⟩
    obtain ⟨g, rfl⟩ := octads_transitive hC
    have hσg : σ * g.val ∈ Subgroup.normalizer (M24 : Set (Equiv.Perm (Fin 24))) :=
      Subgroup.mul_mem _ hσ (Subgroup.le_normalizer g.property)
    change σ • (g • octad) ∈ m24Blocks
    rw [coe_finset_smul, ← mul_smul]
    exact normalizer_image_octad _ hσg
  · intro B hB
    refine ⟨σ⁻¹ • B, ?_, smul_inv_smul σ B⟩
    obtain ⟨g, rfl⟩ := octads_transitive hB
    have hσg : σ⁻¹ * g.val ∈ Subgroup.normalizer (M24 : Set (Equiv.Perm (Fin 24))) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hσ) (Subgroup.le_normalizer g.property)
    rw [coe_finset_smul, ← mul_smul]
    exact normalizer_image_octad _ hσg

end Sporadic.Mathieu.M24OuterRestriction
