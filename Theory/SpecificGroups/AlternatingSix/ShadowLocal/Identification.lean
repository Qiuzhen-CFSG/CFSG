module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification.Embedding
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.HolomorphGeometry.Coordinates

/-!
# The marked Sylow model in the actual automorphism group of A₆

For every Sylow two-subgroup P of Aut(A₆), we construct an equivalence
C₈ ⋊ (Z/8)ˣ ≃ P. It maps the inner dihedral subgroup onto P ∩ Inn(A₆)
and the natural subgroup onto P ∩ S₆. The element marked as a
transposition is induced by an actual transposition of the six letters.

The explicit embedding is conjugated by a permutation-induced
automorphism to obtain the desired Sylow subgroup. The images of r²,
b and c are explicit conjugates of (0123)(45), (45) and (02)(45).
These equations and the subgroup orders establish the two markings;
the cyclic-four, transposition-subgroup and r⁴ equations retain the
embeddings needed by the local geometry.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, printed pp.567–570.
-/

public section
open Subgroup
namespace AlternatingSix.ShadowLocal.Identification

noncomputable def conjugatingPermutation (P : Sylow 2 AutA6) : Equiv.Perm (Fin 6) :=
  Classical.choose (exists_permutation_conjugator P)

private noncomputable def conjugatedEmbedding (P : Sylow 2 AutA6) : Holomorph.Model →* AutA6 :=
  (MulAut.conj (permutationAction (conjugatingPermutation P))).toMonoidHom.comp embedding

private theorem conjugatedEmbedding_injective (P : Sylow 2 AutA6) :
    Function.Injective (conjugatedEmbedding P) :=
  (MulAut.conj (permutationAction (conjugatingPermutation P))).injective.comp embedding_injective

private theorem conjugatedEmbedding_range (P : Sylow 2 AutA6) :
    (conjugatedEmbedding P).range = (P : Subgroup AutA6) := by
  rw [conjugatedEmbedding, MonoidHom.range_comp]
  exact Classical.choose_spec (exists_permutation_conjugator P)

/-- The explicit holomorph, with its markings, inside any actual Sylow subgroup. -/
noncomputable def sylowEquiv (P : Sylow 2 AutA6) : Holomorph.Model ≃* P :=
  (MonoidHom.ofInjective (conjugatedEmbedding_injective P)).trans
    (MulEquiv.subgroupCongr (conjugatedEmbedding_range P))

theorem sylowEquiv_coe (P : Sylow 2 AutA6) (x : Holomorph.Model) :
    (sylowEquiv P x : AutA6) =
      permutationAction (conjugatingPermutation P) * embedding x *
        (permutationAction (conjugatingPermutation P))⁻¹ := by rfl

theorem sylowEquiv_rotation (P : Sylow 2 AutA6) :
    (sylowEquiv P Holomorph.rotation : AutA6) =
      permutationAction (conjugatingPermutation P) * rotation *
        (permutationAction (conjugatingPermutation P))⁻¹ := by
  rw [sylowEquiv_coe, embedding_rotation]

theorem sylowEquiv_rotation_sq (P : Sylow 2 AutA6) :
    (sylowEquiv P (Holomorph.rotation ^ 2) : AutA6) =
      permutationAction (conjugatingPermutation P * dihedralRotation.1 *
        (conjugatingPermutation P)⁻¹) := by
  rw [sylowEquiv_coe, map_pow, embedding_rotation, rotation_sq]
  simp only [map_mul, map_inv]

theorem sylowEquiv_reflection (P : Sylow 2 AutA6) :
    (sylowEquiv P Holomorph.reflection : AutA6) =
      permutationAction (conjugatingPermutation P * dihedralReflection.1 *
        (conjugatingPermutation P)⁻¹) := by
  rw [sylowEquiv_coe, embedding_reflection, reflection]
  simp only [map_mul, map_inv]

theorem sylowEquiv_transposition (P : Sylow 2 AutA6) :
    (sylowEquiv P Holomorph.transposition : AutA6) =
      permutationAction (Equiv.swap (conjugatingPermutation P 4) (conjugatingPermutation P 5)) := by
  rw [sylowEquiv_coe, embedding_transposition, transposition, transpositionPerm,
    Equiv.swap_apply_apply]
  simp only [map_mul, map_inv]

theorem conjugatedTransposition_isSwap (P : Sylow 2 AutA6) :
    (Equiv.swap (conjugatingPermutation P 4) (conjugatingPermutation P 5)).IsSwap :=
  ⟨_, _, (conjugatingPermutation P).injective.ne (by decide), rfl⟩

theorem sylowEquiv_rotation_four (P : Sylow 2 AutA6) :
    (sylowEquiv P (Holomorph.rotation ^ 4) : AutA6) =
      permutationAction (conjugatingPermutation P * (dihedralRotation.1 ^ 2) *
        (conjugatingPermutation P)⁻¹) := by
  rw [sylowEquiv_coe, map_pow, embedding_rotation,
    show 4 = 2 * 2 from rfl, pow_mul, rotation_sq, ← map_pow]
  simp only [map_mul, map_inv]

private theorem conjugate_inner_mem (σ : Equiv.Perm (Fin 6)) (g : A6) :
    permutationAction (σ * g.1 * σ⁻¹) ∈ inner := by
  simp only [map_mul, map_inv]
  exact (inferInstance : inner.Normal).conj_mem _
    ⟨g, (permutationAction_coe g).symm⟩ _

theorem sylowEquiv_innerD (P : Sylow 2 AutA6) :
    Holomorph.innerD.map (sylowEquiv P).toMonoidHom = sylowInner P := by
  apply Subgroup.eq_of_le_of_card_ge
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    change (sylowEquiv P x : AutA6) ∈ inner
    rcases hx with rfl | rfl
    · rw [sylowEquiv_rotation_sq]
      exact conjugate_inner_mem _ _
    · rw [sylowEquiv_reflection]
      exact conjugate_inner_mem _ _
  · rw [Subgroup.card_map_of_injective (sylowEquiv P).injective,
      Nat.card_congr Holomorph.innerEquiv.toEquiv, DihedralGroup.nat_card, sylowInner_card]

theorem sylowEquiv_natural (P : Sylow 2 AutA6) :
    Holomorph.natural.map (sylowEquiv P).toMonoidHom = sylowNatural P := by
  apply Subgroup.eq_of_le_of_card_ge
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    change (sylowEquiv P x : AutA6) ∈ natural
    rcases hx with rfl | rfl | rfl
    · rw [sylowEquiv_rotation_sq]
      exact ⟨_, rfl⟩
    · rw [sylowEquiv_transposition]
      exact ⟨_, rfl⟩
    · rw [sylowEquiv_reflection]
      exact ⟨_, rfl⟩
  · rw [Subgroup.card_map_of_injective (sylowEquiv P).injective,
      Nat.card_congr Holomorph.naturalEquiv.toEquiv, Nat.card_prod,
      DihedralGroup.nat_card, sylowNatural_card]
    norm_num [Nat.card_eq_fintype_card, Holomorph.C2]

theorem sylowEquiv_cyclicFour (P : Sylow 2 AutA6) :
    Holomorph.cyclicFour.map (sylowEquiv P).toMonoidHom =
      Subgroup.zpowers (sylowEquiv P (Holomorph.rotation ^ 2)) :=
  (sylowEquiv P).toMonoidHom.map_zpowers _

theorem sylowEquiv_transpositionSubgroup (P : Sylow 2 AutA6) :
    Holomorph.transpositionSubgroup.map (sylowEquiv P).toMonoidHom =
      Subgroup.zpowers (sylowEquiv P Holomorph.transposition) :=
  (sylowEquiv P).toMonoidHom.map_zpowers _

/-- The cyclic four subgroup, as an actual subgroup of Aut(A₆). -/
theorem sylowEquiv_cyclicFour_image (P : Sylow 2 AutA6) :
    (Holomorph.cyclicFour.map (sylowEquiv P).toMonoidHom).map
        (P : Subgroup AutA6).subtype =
      Subgroup.zpowers (permutationAction
        (conjugatingPermutation P * dihedralRotation.1 * (conjugatingPermutation P)⁻¹)) := by
  rw [sylowEquiv_cyclicFour, MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers (sylowEquiv_rotation_sq P)

/-- The marked order-two subgroup is generated by a genuine transposition. -/
theorem sylowEquiv_transpositionSubgroup_image (P : Sylow 2 AutA6) :
    (Holomorph.transpositionSubgroup.map (sylowEquiv P).toMonoidHom).map
        (P : Subgroup AutA6).subtype =
      Subgroup.zpowers (permutationAction
        (Equiv.swap (conjugatingPermutation P 4) (conjugatingPermutation P 5))) := by
  rw [sylowEquiv_transpositionSubgroup, MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers (sylowEquiv_transposition P)

/-- Every Sylow two-subgroup of the actual automorphism group has the
marked holomorph model, including the genuine permutation transposition. -/
theorem exists_marked_sylow_equiv (P : Sylow 2 AutA6) :
    ∃ (e : Holomorph.Model ≃* P) (τ : Equiv.Perm (Fin 6)),
      τ.IsSwap ∧
      Holomorph.innerD.map e.toMonoidHom = sylowInner P ∧
      Holomorph.natural.map e.toMonoidHom = sylowNatural P ∧
      (e Holomorph.transposition : AutA6) = permutationAction τ :=
  ⟨sylowEquiv P, _, conjugatedTransposition_isSwap P,
    sylowEquiv_innerD P, sylowEquiv_natural P, sylowEquiv_transposition P⟩

end AlternatingSix.ShadowLocal.Identification
