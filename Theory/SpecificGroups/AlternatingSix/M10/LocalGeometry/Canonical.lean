module
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.Coordinates
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification.Embedding

/-!
# The concrete semidihedral complement and quaternion intersection

The intrinsic order-sixteen subgroup is embedded in the genuine Aut(A₆).
Its center is the image of (02)(13), and its intersection with the specified
M₁₀ extension is the image of an explicitly embedded quaternion group.
The reflection (02)(45) supplies the involution normalizing the complement.

Source: Aschbacher, A 2-local characterization of M12 (2003), 4.9–4.10,
pp.41–42. The full nine-group normalizer calculation is a separate input.
-/

@[expose] public section
namespace AlternatingSix.M10.LocalGeometry
open Subgroup ShadowLocal

noncomputable def standardComplement : Subgroup AutA6 :=
  Coordinates.complement.map Identification.embedding

noncomputable def standardQuaternion : Subgroup AutA6 :=
  Coordinates.quaternionEmbedding.range.map Identification.embedding

theorem card_standardComplement : Nat.card standardComplement = 16 := by
  rw [standardComplement, card_map_of_injective Identification.embedding_injective,
    Coordinates.card_complement]

theorem embedding_flip : Identification.embedding Coordinates.flip =
    permutationAction standardZ := by
  rw [Coordinates.flip, map_mul, Identification.embedding_transposition,
    Identification.embedding_reflection]
  change permutationAction Identification.transpositionPerm *
    permutationAction dihedralReflection.1 = permutationAction standardZ
  rw [← map_mul]
  congr 1
  decide +kernel

theorem embedding_central : Identification.embedding (Holomorph.rotation ^ 4) =
    permutationAction (standardU * standardZ) := by
  rw [map_pow, Identification.embedding_rotation, show 4 = 2 * 2 from rfl,
    pow_mul, Identification.rotation_sq, ← map_pow]
  congr 1
  decide +kernel

theorem standardComplement_semidihedral :
    ∃ p q : standardComplement, orderOf p = 8 ∧ orderOf q = 2 ∧
      q * p * q⁻¹ = p ^ 3 ∧ zpowers p ⊔ zpowers q = ⊤ := by
  let e : Coordinates.complement ≃* standardComplement := Coordinates.complement.equivMapOfInjective Identification.embedding
    Identification.embedding_injective
  refine ⟨e Coordinates.rotationIn, e Coordinates.flipIn,
    (e.orderOf_eq _).trans Coordinates.rotationIn_order,
    (e.orderOf_eq _).trans Coordinates.flipIn_order, ?_, ?_⟩
  · simpa only [map_mul, map_inv, map_pow] using congrArg e Coordinates.flipIn_rotationIn
  · have he := congrArg (Subgroup.map e.toMonoidHom) Coordinates.complement_generated
    simpa only [Subgroup.map_sup, MonoidHom.map_zpowers,
      map_top_of_surjective e.toMonoidHom e.surjective, MulEquiv.coe_toMonoidHom] using he

theorem standardZ_mem_complement : permutationAction standardZ ∈ standardComplement := by
  rw [← embedding_flip]
  exact mem_map_of_mem _ Coordinates.flip_mem

theorem center_standardComplement :
    (center standardComplement).map standardComplement.subtype =
      zpowers (permutationAction (standardU * standardZ)) := by
  rw [standardComplement, ← map_embeddedCenter _ _ Identification.embedding_injective,
    Coordinates.center_complement, Holomorph.centralTwo, MonoidHom.map_zpowers,
    embedding_central]

theorem permutationAction_mem_inner_iff (σ : Equiv.Perm (Fin 6)) :
    permutationAction σ ∈ ShadowLocal.inner ↔ σ ∈ alternatingGroup (Fin 6) := by
  constructor
  · rintro ⟨a, ha⟩
    have he : (a : Equiv.Perm (Fin 6)) = σ :=
      permutationAction_injective ((permutationAction_coe a).trans ha)
    exact he ▸ a.property
  · intro hσ
    exact ⟨⟨σ, hσ⟩, (permutationAction_coe ⟨σ, hσ⟩).symm⟩

private theorem extension_generator_sq_inner :
    (Identification.rotation * Identification.transposition) ^ 2 ∈ ShadowLocal.inner := by
  have hm : (Holomorph.rotation * Holomorph.transposition) ^ 2 =
      (Holomorph.rotation ^ 2) ^ 3 := by decide +kernel
  have he := congrArg Identification.embedding hm
  simp only [map_pow, map_mul, Identification.embedding_rotation,
    Identification.embedding_transposition, Identification.rotation_sq] at he
  rw [he]
  apply Subgroup.pow_mem
  exact (permutationAction_mem_inner_iff _).mpr dihedralRotation.property

private theorem extension_generator_not_natural :
    Identification.rotation * Identification.transposition ∉ natural := by
  intro h
  apply Identification.rotation_not_mem_natural
  have ht : Identification.transposition ∈ natural := ⟨Identification.transpositionPerm, rfl⟩
  simpa only [mul_inv_cancel_right] using natural.mul_mem h (natural.inv_mem ht)

/-- The intersection with the natural S₆ is precisely its alternating subgroup. -/
theorem inner_of_extension_of_natural (a : AutA6) (ha : a ∈ extension) (hn : a ∈ natural) :
    a ∈ ShadowLocal.inner := by
  classical
  let q := QuotientGroup.mk' ShadowLocal.inner
  let t := Identification.rotation * Identification.transposition
  have ht2 : q t ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr extension_generator_sq_inner
  have htne : q t ≠ 1 := by
    intro he
    exact extension_generator_not_natural
      (inner_le_natural ((QuotientGroup.eq_one_iff _).mp he))
  have hto : orderOf (q t) = 2 := orderOf_eq_prime ht2 htne
  have himage : extension.map q ≤ zpowers (q t) := by
    rw [extension, Subgroup.map_sup, MonoidHom.map_zpowers]
    apply sup_le _ le_rfl
    rintro _ ⟨x, hx, rfl⟩
    have he : q x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
    rw [he]
    exact one_mem _
  have he := himage (mem_map_of_mem q ha)
  rw [mem_zpowers_iff_mem_range_orderOf, hto, Finset.mem_image] at he
  obtain ⟨k, hk, he⟩ := he
  have hk' : k < 2 := Finset.mem_range.mp hk
  interval_cases k
  · apply (QuotientGroup.eq_one_iff _).mp
    exact he.symm
  · have he' : q a = q t := by simpa only [pow_one] using he.symm
    have hprod : a * t⁻¹ ∈ ShadowLocal.inner := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (a * t⁻¹) = 1
      rw [map_mul, map_inv, he', mul_inv_cancel]
    have hti : t⁻¹ ∈ natural := by
      simpa only [inv_mul_cancel_left] using
        natural.mul_mem (natural.inv_mem hn) (inner_le_natural hprod)
    exact (extension_generator_not_natural (natural.inv_mem hti)).elim

theorem standardZ_not_extension : permutationAction standardZ ∉ extension := by
  intro h
  have hi := (permutationAction_mem_inner_iff _).mp
    (inner_of_extension_of_natural _ h ⟨standardZ, rfl⟩)
  have hn : standardZ ∉ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  exact hn hi

private theorem quaternion_word (x : QuaternionGroup 2) :
    Coordinates.quaternionEmbedding x ∈ Coordinates.complement ∧
      ∃ (i : Fin 4) (j : Fin 2), Coordinates.quaternionEmbedding x =
        (Holomorph.rotation * Coordinates.flip) ^ j.val * (Holomorph.rotation ^ 2) ^ i.val := by
  revert x
  decide +kernel

theorem standardQuaternion_le : standardQuaternion ≤ standardComplement ⊓ extension := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  obtain ⟨hc, i, j, he⟩ := quaternion_word x
  refine ⟨mem_map_of_mem _ hc, ?_⟩
  rw [he, map_mul, map_pow, map_pow, map_pow, map_mul,
    Identification.embedding_rotation, Coordinates.flip, map_mul,
    Identification.embedding_transposition, Identification.embedding_reflection]
  apply extension.mul_mem
  · apply Subgroup.pow_mem
    have hc : Identification.reflection ∈ extension :=
      (show ShadowLocal.inner ≤ extension from le_sup_left)
        ((permutationAction_mem_inner_iff _).mpr dihedralReflection.property)
    have ht : Identification.rotation * Identification.transposition ∈ extension :=
      (show zpowers (Identification.rotation * Identification.transposition) ≤ extension
        from le_sup_right) (mem_zpowers _)
    simpa only [mul_assoc] using extension.mul_mem ht hc
  · apply Subgroup.pow_mem
    rw [Identification.rotation_sq]
    exact (show ShadowLocal.inner ≤ extension from le_sup_left)
      ((permutationAction_mem_inner_iff _).mpr dihedralRotation.property)

theorem standardComplement_inf_extension : standardComplement ⊓ extension = standardQuaternion := by
  apply le_antisymm _ standardQuaternion_le
  rintro a ⟨⟨x, hx, rfl⟩, he⟩
  have hcases : ∀ x : Holomorph.Model, x ∈ Coordinates.complement →
      (∃ y, Coordinates.quaternionEmbedding y = x) ∨
      ∃ y, Coordinates.quaternionEmbedding y * Coordinates.flip = x := by decide +kernel
  rcases hcases x hx with h | ⟨y, rfl⟩
  · exact mem_map_of_mem _ h
  · exfalso
    apply standardZ_not_extension
    have hy : Identification.embedding (Coordinates.quaternionEmbedding y) ∈ extension :=
      (standardQuaternion_le (mem_map_of_mem _ ⟨y, rfl⟩)).2
    rw [map_mul, embedding_flip] at he
    exact (extension.mul_mem_cancel_left hy).mp he

noncomputable def standardQuaternionEquiv :
    ↥(standardComplement ⊓ extension) ≃* QuaternionGroup 2 :=
  (MulEquiv.subgroupCongr standardComplement_inf_extension).trans
    ((Coordinates.quaternionEmbedding.range.equivMapOfInjective Identification.embedding
      Identification.embedding_injective).symm.trans
        (MonoidHom.ofInjective Coordinates.quaternionEmbedding_injective).symm)

theorem standardComplement_disjoint : Disjoint (nine standardNine) standardComplement := by
  apply disjoint_of_coprime_natCard
  rw [nine, card_map_of_injective permutationAction_injective,
    card_standardNine, card_standardComplement]
  decide

theorem reflection_mem_extension : Identification.reflection ∈ extension :=
  (show ShadowLocal.inner ≤ extension from le_sup_left)
    ((permutationAction_mem_inner_iff _).mpr dihedralReflection.property)

theorem reflection_not_complement : Identification.reflection ∉ standardComplement := by
  rw [← Identification.embedding_reflection]
  intro h
  exact Coordinates.reflection_not_mem ((mem_map_iff_mem Identification.embedding_injective).mp h)

theorem reflection_normalizes_complement :
    Identification.reflection ∈ normalizer (standardComplement : Set AutA6) := by
  rw [← Identification.embedding_reflection]
  exact Coordinates.complement.le_normalizer_map Identification.embedding
    (mem_map_of_mem _ Coordinates.reflection_normalizes)

private theorem rotation_conjugates (p : Equiv.Perm (Fin 6)) :
    Identification.rotation * permutationAction p * Identification.rotation⁻¹ =
      permutationAction (Identification.twistHom p) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  change GLS3.Chapter5.outerHom
      (Identification.twist * (p * g.1 * p⁻¹) * Identification.twist⁻¹) =
    Identification.twistHom p * GLS3.Chapter5.outerHom
      (Identification.twist * g.1 * Identification.twist⁻¹) *
        (Identification.twistHom p)⁻¹
  simp only [Identification.twistHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, map_mul, map_inv]
  group

theorem rotation_normalizes_nine :
    Identification.rotation ∈ normalizer (nine standardNine : Set AutA6) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
    change Identification.rotation * permutationAction (nineEmbedding i) *
      Identification.rotation⁻¹ ∈ nine standardNine
    rw [rotation_conjugates]
    have ht : ∀ i : NineCoordinates, ∃ j : NineCoordinates,
        nineEmbedding j = Identification.twistHom (nineEmbedding i) := by decide +kernel
    obtain ⟨j, hj⟩ := ht i
    exact ⟨nineEmbedding j, ⟨j, rfl⟩, congrArg permutationAction hj⟩
  · rw [card_map_of_injective (MulAut.conj Identification.rotation).injective]

theorem standardComplement_le_normalizer :
    standardComplement ≤ normalizer (nine standardNine : Set AutA6) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, j, rfl⟩ := Coordinates.complement_normal_form x hx
  rw [map_mul, map_pow, map_pow, Identification.embedding_rotation, embedding_flip]
  apply Subgroup.mul_mem
  · exact Subgroup.pow_mem _ rotation_normalizes_nine _
  · exact Subgroup.pow_mem _
      (standardNine.le_normalizer_map permutationAction
        (mem_map_of_mem _ standardZ_normalizes)) _

theorem standardNormalizer_lower :
    nine standardNine ⊔ standardComplement ≤ normalizer (nine standardNine : Set AutA6) :=
  sup_le (nine standardNine).le_normalizer standardComplement_le_normalizer

/-- The chosen inner reflection moves the literal nine-group. -/
theorem reflection_not_stabilizer : Identification.reflection ∉ stabilizer standardNine := by
  rintro ⟨_, hn⟩
  have he : (normalizer (nine standardNine : Set AutA6)).comap permutationAction =
      normalizer (standardNine : Set (Equiv.Perm (Fin 6))) := by
    rw [nine, comap_normalizer_eq_of_le_range (standardNine.map_le_range permutationAction),
      comap_map_eq_self_of_injective permutationAction_injective]
  have hp : dihedralReflection.1 ∈ normalizer (standardNine : Set (Equiv.Perm (Fin 6))) := by
    rw [← he]
    exact hn
  have hx : cycle₀ ∈ standardNine := ⟨(.ofAdd 1, 1), by decide +kernel⟩
  obtain ⟨i, hi⟩ := (mem_normalizer_iff.mp hp cycle₀).mp hx
  have hnot : ∀ i : NineCoordinates,
      nineEmbedding i ≠ dihedralReflection.1 * cycle₀ * dihedralReflection.1⁻¹ := by
    decide +kernel
  exact hnot i hi

end AlternatingSix.M10.LocalGeometry
