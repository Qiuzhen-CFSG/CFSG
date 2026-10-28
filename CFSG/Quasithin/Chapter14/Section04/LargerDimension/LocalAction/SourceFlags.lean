module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.MarkedGeometry
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Structure

/-!
# The source flags and marked parabolics in 14.4.8

This module records the source-facing calculation on pp. 1009 and 1012.  The
natural-module facts are kept as hypotheses of the outer 14.3.10 assembly; the
conclusions below are the literal family membership, joins and index
calculation.  The full action premise is the actual conjugation action on the
moved elementary group.  Its quotient map is retained, together with the
images and preimages of each marked subgroup.

The six maximality conclusions are obtained by quotient correspondence from
the concrete PSL₃(2) and S₃ × S₃ parabolic coatoms.  No A₃ record, family tag,
or assumed maximality is used.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.3.10 and Lemmas 14.4.8, 14.4.13, printed pp. 997, 1009 and 1012.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter14.Section04.LargerDimension
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction

universe u

variable {G : Type u} [Group G] [Finite G]

abbrev PSL3Two := Matrix.PSL3Two.PSL
abbrev SymmetricThree := SymmetricThreeProduct.G

/-- The actual quotient map attached to a marked vertex. -/
noncomputable def quotientMap (J : Subgroup G) (e : coreQuotient J ≃* PSL3Two) :
    J →* PSL3Two := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))

noncomputable def productQuotientMap (J : Subgroup G)
    (e : coreQuotient J ≃* SymmetricThree) : J →* SymmetricThree :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))

/-! ### The source facts and the full action premise -/

/-- Output identities for the original natural flag. The constructor in
`NaturalFlags.Construction` proves them from the earlier natural action and
the actual invariant flag. This record alone is not Hypothesis 14.3.10. -/
structure NaturalFlagData
    (H : Subgroup G) (T : Sylow 2 G)
    (V₁ V₂ V E L L₁ L₂ : Subgroup G) : Prop where
  H_eq_normalizer : H = normalizer (V₁ : Set G)
  L₁_three : ThreeExtension H (T : Subgroup G) L₁
  moved_eq : movedSpace V₂ L₁ = V
  moved_card : Nat.card V = 8
  moved_le_E : V ≤ E
  V₁_le_moved : V₁ ≤ V
  L₂_three : ThreeExtension L (T : Subgroup G) L₂
  L₁_le_L : L₁ ≤ L
  L₂_le_L : L₂ ≤ L
  generated : L₁ ⊔ L₂ = L
  flag_intersection :
    (L ⊔ (T : Subgroup G)) ⊓ H = L₁ ⊔ (T : Subgroup G)

/-- The full conjugation action allowed by the outer full-action producer.
`action_eq_conjugation` forces the stored map to be the literal ambient
conjugation map, and `quotient_map_eq` records the literal quotient map rather
than an unattached isomorphism of abstract groups. -/
structure FullActionData
    (H L₂ : Subgroup G) (T : Sylow 2 G) (V₂ E Z : Subgroup G)
    (hZ : Z ∈ YFamily H (T : Subgroup G) V₂ E) where
  normalizes : localJoin L₂ Z ⊔ (T : Subgroup G) ≤
    normalizer (movedSpace V₂ Z : Set G)
  action : (localJoin L₂ Z ⊔ (T : Subgroup G) : Subgroup G) →*
    MulAut (movedSpace V₂ Z)
  action_eq_conjugation : action = conjugation _ _ normalizes
  action_surjective : Function.Surjective action
  action_kernel : action.ker =
    pCore 2 ((localJoin L₂ Z ⊔ (T : Subgroup G) : Subgroup G) : Type u)
  model : MulAut (movedSpace V₂ Z) ≃* PSL3Two
  quotient : coreQuotient (localJoin L₂ Z ⊔ (T : Subgroup G)) ≃* PSL3Two
  quotient_map_eq : quotientMap (localJoin L₂ Z ⊔ (T : Subgroup G)) quotient =
    model.toMonoidHom.comp action

/-- A literal marking of the two maximal subgroups in a PSL₃(2) vertex. -/
structure LinearMarking (J A B : Subgroup G)
    (e : coreQuotient J ≃* PSL3Two) where
  A_le : A ≤ J
  B_le : B ≤ J
  A_model : Subgroup PSL3Two
  B_model : Subgroup PSL3Two
  A_model_is_parabolic : A_model = Matrix.PSL3Two.pointParabolic ∨
    A_model = Matrix.PSL3Two.lineParabolic
  B_model_is_parabolic : B_model = Matrix.PSL3Two.pointParabolic ∨
    B_model = Matrix.PSL3Two.lineParabolic
  A_preimage : A.subgroupOf J = A_model.comap (quotientMap J e)
  B_preimage : B.subgroupOf J = B_model.comap (quotientMap J e)
  A_image : (A.subgroupOf J).map (quotientMap J e) = A_model
  B_image : (B.subgroupOf J).map (quotientMap J e) = B_model

/-- A literal marking of the two maximal subgroups in an S₃ × S₃ vertex. -/
structure ProductMarking (J A B : Subgroup G)
    (e : coreQuotient J ≃* SymmetricThree) where
  A_le : A ≤ J
  B_le : B ≤ J
  A_model : Subgroup SymmetricThree
  B_model : Subgroup SymmetricThree
  A_model_is_parabolic : A_model = SymmetricThreeProduct.leftParabolic ∨
    A_model = SymmetricThreeProduct.rightParabolic
  B_model_is_parabolic : B_model = SymmetricThreeProduct.leftParabolic ∨
    B_model = SymmetricThreeProduct.rightParabolic
  A_preimage : A.subgroupOf J = A_model.comap (productQuotientMap J e)
  B_preimage : B.subgroupOf J = B_model.comap (productQuotientMap J e)
  A_image : (A.subgroupOf J).map (productQuotientMap J e) = A_model
  B_image : (B.subgroupOf J).map (productQuotientMap J e) = B_model

/-! ### The source index and quotient-coatom calculations -/

/-- The 12.8.9 source residual is used only after adjoining the Sylow
subgroup.  Thus `I₂` itself remains separate from the marked parabolic
`L₂T`. -/
lemma source_I₂_marked_join_T {G : Type u} [Group G]
    (I₂ L₂ U : Subgroup G) (T : Sylow 2 G)
    (hI : I₂ = L₂ ⊔ U) (hUT : U ≤ (T : Subgroup G)) :
    I₂ ⊔ (T : Subgroup G) = L₂ ⊔ (T : Subgroup G) := by
  exact source_I₂_join_T I₂ L₂ U (T : Subgroup G) hI hUT

/-- A source cubic extension has index three after adjoining its normalizing
Sylow subgroup.  This is the literal 12.8.9/14.4.8 index calculation. -/
theorem source_index_three {H : Subgroup G} (T : Sylow 2 G) (X : Subgroup G)
    (hX : ThreeExtension H T X) :
    ((T : Subgroup G).subgroupOf (X ⊔ (T : Subgroup G))).index = 3 := by
  have hcore : twoCore X ≤ (T : Subgroup G) := by
    have hn : (T : Subgroup G) ≤ normalizer (twoCore X : Set G) :=
      hX.T_normalizes.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
    have hp : IsPGroup 2 (twoCore X ⊔ (T : Subgroup G) : Subgroup G) :=
      (isPGroup_pCoreIn 2 X).to_sup_of_normal_left' T.isPGroup' hn
    exact le_sup_left.trans (T.is_maximal' hp le_sup_right).le
  have hidx : (pCore 2 X).index = 3 := by
    have he := relIndex_map_map_of_injective (pCore 2 X) ⊤ X.subtype_injective
    rw [← MonoidHom.range_eq_map, range_subtype, relIndex_top_right] at he
    exact ((pCore 2 X).index_eq_card.symm.trans he.symm).trans hX.index_three
  let S : Sylow 2 X := pCore_isPGroup.toSylow (by rw [hidx]; decide)
  have hinf : X ⊓ (T : Subgroup G) = twoCore X := by
    have hh := inf_eq_sylow_map S T.isPGroup' hcore
    exact (inf_comm X (T : Subgroup G)).trans hh
  have hcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes X (T : Subgroup G)
    hX.T_normalizes
  rw [hinf] at hcard
  have h1 := relIndex_mul_relIndex (⊥ : Subgroup G) (twoCore X) X bot_le (map_subtype_le _)
  simp only [relIndex_bot_left, hX.index_three] at h1
  have h2 := relIndex_mul_relIndex (⊥ : Subgroup G) (T : Subgroup G)
    (X ⊔ (T : Subgroup G)) bot_le le_sup_right
  simp only [relIndex_bot_left] at h2
  rw [← h1, ← h2, mul_assoc] at hcard
  have hh := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := twoCore X)) hcard
  rw [mul_comm 3] at hh
  exact (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (T : Subgroup G))) hh).symm

private theorem linear_model_coatom (P : Subgroup PSL3Two)
    (hP : P = Matrix.PSL3Two.pointParabolic ∨
      P = Matrix.PSL3Two.lineParabolic) : IsCoatom P := by
  rcases hP with rfl | rfl
  · exact Matrix.PSL3Two.isCoatom_pointParabolic
  · exact Matrix.PSL3Two.isCoatom_lineParabolic

private theorem product_model_coatom (P : Subgroup SymmetricThree)
    (hP : P = SymmetricThreeProduct.leftParabolic ∨
      P = SymmetricThreeProduct.rightParabolic) : IsCoatom P := by
  rcases hP with rfl | rfl
  · exact SymmetricThreeProduct.leftParabolic_isCoatom
  · exact SymmetricThreeProduct.rightParabolic_isCoatom

omit [Finite G] in
theorem linear_marking_coatoms {J A B : Subgroup G}
    {e : coreQuotient J ≃* PSL3Two} (h : LinearMarking J A B e) :
    IsCoatom (A.subgroupOf J) ∧ IsCoatom (B.subgroupOf J) := by
  have hf : Function.Surjective (quotientMap J e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  refine ⟨?_, ?_⟩
  · rw [h.A_preimage]
    exact Subgroup.isCoatom_comap_of_surjective hf
      (linear_model_coatom h.A_model h.A_model_is_parabolic)
  · rw [h.B_preimage]
    exact Subgroup.isCoatom_comap_of_surjective hf
      (linear_model_coatom h.B_model h.B_model_is_parabolic)

omit [Finite G] in
theorem product_marking_coatoms {J A B : Subgroup G}
    {e : coreQuotient J ≃* SymmetricThree} (h : ProductMarking J A B e) :
    IsCoatom (A.subgroupOf J) ∧ IsCoatom (B.subgroupOf J) := by
  have hf : Function.Surjective (productQuotientMap J e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  refine ⟨?_, ?_⟩
  · rw [h.A_preimage]
    exact Subgroup.isCoatom_comap_of_surjective hf
      (product_model_coatom h.A_model h.A_model_is_parabolic)
  · rw [h.B_preimage]
    exact Subgroup.isCoatom_comap_of_surjective hf
      (product_model_coatom h.B_model h.B_model_is_parabolic)

/-! ### The complete source-flag conclusion -/

structure SourceFlagsConclusion
    (H : Subgroup G) (T : Sylow 2 G)
    (V₁ V₂ V E L L₁ L₂ X : Subgroup G) where
  L₁_mem_Y : L₁ ∈ YFamily H (T : Subgroup G) V₂ E
  H_eq_normalizer : H = normalizer (V₁ : Set G)
  moved_eq : movedSpace V₂ L₁ = V
  flag_intersection :
    (L ⊔ (T : Subgroup G)) ⊓ H = L₁ ⊔ (T : Subgroup G)
  localJoin_eq : localJoin L₂ L₁ = L
  index_three : ((T : Subgroup G).subgroupOf (L₁ ⊔ (T : Subgroup G))).index = 3
  L₁_three : ThreeExtension H (T : Subgroup G) L₁
  L₂_three : ThreeExtension L (T : Subgroup G) L₂
  X_three : ThreeExtension H (T : Subgroup G) X
  quotient₁ : coreQuotient (L ⊔ (T : Subgroup G)) ≃* PSL3Two
  quotient₂ : coreQuotient (L₁ ⊔ X ⊔ (T : Subgroup G)) ≃* SymmetricThree
  quotient₃ : coreQuotient (localJoin L₂ X ⊔ (T : Subgroup G)) ≃* PSL3Two
  maximal₁₁ : IsCoatom ((L₁ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G)))
  maximal₁₂ : IsCoatom ((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G)))
  maximal₂₁ : IsCoatom ((L₁ ⊔ (T : Subgroup G)).subgroupOf
    (L₁ ⊔ X ⊔ (T : Subgroup G)))
  maximal₂₂ : IsCoatom ((X ⊔ (T : Subgroup G)).subgroupOf
    (L₁ ⊔ X ⊔ (T : Subgroup G)))
  maximal₃₁ : IsCoatom ((L₂ ⊔ (T : Subgroup G)).subgroupOf
    (localJoin L₂ X ⊔ (T : Subgroup G)))
  maximal₃₂ : IsCoatom ((X ⊔ (T : Subgroup G)).subgroupOf
    (localJoin L₂ X ⊔ (T : Subgroup G)))
  full_action_L₁ : ∃ hZ : L₁ ∈ YFamily H (T : Subgroup G) V₂ E,
    Nonempty (FullActionData H L₂ T V₂ E L₁ hZ)
  full_action_X : ∃ hZ : X ∈ YFamily H (T : Subgroup G) V₂ E,
    Nonempty (FullActionData H L₂ T V₂ E X hZ)
  distinct : X ≠ L₁

/-!
The middle quotient and the six literal markings are supplied by the source
model calculation.  The theorem below discharges all structural fields around
them and extracts the concrete coatom facts used by `source_dSystem...`.
-/

noncomputable def source_flags
    (H : Subgroup G) (T : Sylow 2 G)
    (V₁ V₂ V E L L₁ L₂ X : Subgroup G)
    (hN : NaturalFlagData H T V₁ V₂ V E L L₁ L₂)
    (hX : X ∈ YFamily H (T : Subgroup G) V₂ E) (hne : X ≠ L₁)
    (full : ∀ (Z : Subgroup G) (hZ : Z ∈ YFamily H (T : Subgroup G) V₂ E),
      FullActionData H L₂ T V₂ E Z hZ)
    (e₁ : coreQuotient (L ⊔ (T : Subgroup G)) ≃* PSL3Two)
    (e₂ : coreQuotient (L₁ ⊔ X ⊔ (T : Subgroup G)) ≃* SymmetricThree)
    (mark₁ : LinearMarking (L ⊔ (T : Subgroup G))
      (L₁ ⊔ (T : Subgroup G)) (L₂ ⊔ (T : Subgroup G))
      e₁)
    (mark₂ : ProductMarking (L₁ ⊔ X ⊔ (T : Subgroup G))
      (L₁ ⊔ (T : Subgroup G)) (X ⊔ (T : Subgroup G)) e₂)
    (e₃ : coreQuotient (localJoin L₂ X ⊔ (T : Subgroup G)) ≃* PSL3Two)
    (mark₃ : LinearMarking (localJoin L₂ X ⊔ (T : Subgroup G))
      (L₂ ⊔ (T : Subgroup G)) (X ⊔ (T : Subgroup G)) e₃) :
    SourceFlagsConclusion H T V₁ V₂ V E L L₁ L₂ X := by
  have hL₁Y : L₁ ∈ YFamily H T V₂ E := by
    refine ⟨hN.L₁_three, ?_, ?_⟩
    · rw [hN.moved_eq, hN.moved_card]
    · rw [hN.moved_eq]
      exact hN.moved_le_E
  have hjoin : localJoin L₂ L₁ = L := by
    dsimp [localJoin]
    rw [sup_comm, hN.generated]
  have hi := source_index_three T L₁ hN.L₁_three
  have hfull₁ : ∃ hZ : L₁ ∈ YFamily H (T : Subgroup G) V₂ E,
      Nonempty (FullActionData H L₂ T V₂ E L₁ hZ) :=
    ⟨hL₁Y, ⟨full L₁ hL₁Y⟩⟩
  have hfullX : ∃ hZ : X ∈ YFamily H (T : Subgroup G) V₂ E,
      Nonempty (FullActionData H L₂ T V₂ E X hZ) :=
    ⟨hX, ⟨full X hX⟩⟩
  have hm₁ := linear_marking_coatoms mark₁
  have hm₂ := product_marking_coatoms mark₂
  have hm₃ := linear_marking_coatoms mark₃
  refine {
    L₁_mem_Y := hL₁Y
    H_eq_normalizer := hN.H_eq_normalizer
    moved_eq := hN.moved_eq
    flag_intersection := hN.flag_intersection
    localJoin_eq := hjoin
    index_three := hi
    L₁_three := hN.L₁_three
    L₂_three := hN.L₂_three
    X_three := hX.1
    quotient₁ := e₁
    quotient₂ := e₂
    quotient₃ := e₃
    maximal₁₁ := hm₁.1
    maximal₁₂ := hm₁.2
    maximal₂₁ := hm₂.1
    maximal₂₂ := hm₂.2
    maximal₃₁ := hm₃.1
    maximal₃₂ := hm₃.2
    full_action_L₁ := hfull₁
    full_action_X := hfullX
    distinct := hne }

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
