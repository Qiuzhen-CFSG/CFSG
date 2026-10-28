module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree.Hyperplane
public import Theory.Representation.BinaryOffender.PerfectMoved
/-!
# Excluding the exceptional four-dimensional factor from B.6.9

The original exceptional source row contains a natural binary three-space
which is exactly its moved space. Perfect-actor commutator idempotence
identifies that space with the actual factor's moved space in V/C_V(Y).
The resulting full-normalizer natural chart contradicts minimal parabolicity.
This proves, for both same original factors, the exact natural SL2 or
symmetric-five quotient row; the extension is not assumed to split.

Source: Aschbacher–Smith, B.5.6(3c), B.4.8(3), B.6.9, pp.105,91,116.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The literal exceptional row has actual factor displacement dimension three. -/
theorem fourDimensionalSource_moved_finrank
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Subrepresentation ρ) (hU : moved ρ A ≤ U.toSubmodule)
    (c : FourDimensionalSource (U.toRepresentation.comp A.subtype)) :
    Module.finrank (ZMod 2) (moved ρ A) = 3 := by
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) BinaryField.two.Carrier) :=
    Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := c.natural.groupEquiv.symm.toMonoidHom)
      c.natural.groupEquiv.symm.surjective
  have hm₁ : moved (U.toRepresentation.comp A.subtype) ⊤ =
      subspaceCommutator U.toRepresentation ⊤ A := by
    have hh := subspaceCommutator_map_embedding (U.toRepresentation.comp A.subtype)
      U.toRepresentation A.subtype (LinearMap.id : U.toSubmodule →ₗ[ZMod 2] U.toSubmodule)
      (fun _ _ => rfl) ⊤ ⊤
    simpa only [Submodule.map_id, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hm₂ : subspaceCommutator ρ U.toSubmodule A =
      (subspaceCommutator U.toRepresentation ⊤ A).map U.toSubmodule.subtype := by
    have hh := subspaceCommutator_map_embedding ρ U.toRepresentation (MonoidHom.id G)
      U.toSubmodule.subtype (fun _ _ => rfl) A ⊤
    simpa only [Submodule.map_top, Submodule.range_subtype, Subgroup.map_id] using hh
  have hm : c.space.toSubmodule.map U.toSubmodule.subtype = moved ρ A := by
    rw [c.space_eq, hm₁, ← hm₂]
    exact subspaceCommutator_eq_moved_of_contains_moved ρ A U.toSubmodule hU
  have hd : Module.finrank (ZMod 2) c.space.toSubmodule = 3 := by
    have hh := c.natural.linearEquiv.finrank_eq
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Fin 3 → BinaryField.two.Carrier)
    have hdModel : Module.finrank (ZMod 2) (Fin 3 → BinaryField.two.Carrier) = 3 := by
      apply Nat.pow_right_injective (by decide : 1 < 2)
      simpa [BinaryField.two] using hcard.symm
    exact hh.trans hdModel
  have he := (Submodule.equivMapOfInjective U.toSubmodule.subtype
    U.toSubmodule.subtype_injective c.space.toSubmodule).finrank_eq
  rw [hm] at he
  exact he.symm.trans hd

set_option backward.isDefEq.respectTransparency false in
/-- The full normalizer action excludes the original nonsplit exceptional row. -/
theorem source_exceptional_four_factor_excluded
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (A : Subgroup Y) [A.Normal]
    (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (U : Subrepresentation (ρ.comp Y.subtype))
    (hU : moved (ρ.comp Y.subtype) A ≤ U.toSubmodule)
    (c : FourDimensionalSource
      (((fixed (ρ.comp Y.subtype)).quotientImage U).toRepresentation.comp A.subtype)) :
    False := by
  let σ := ρ.comp Y.subtype
  let τ := (fixed σ).quotientRepresentation
  let E := (fixed σ).quotientImage U
  have hE : moved τ A ≤ E.toSubmodule := by
    have hm := subspaceCommutator_map_embedding τ σ (MonoidHom.id Y)
      (fixed σ).toSubmodule.mkQ (fun _ _ => rfl) A ⊤
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
      Subgroup.map_id] at hm
    exact hm.trans_le (Submodule.map_mono hU)
  have hd : Module.finrank (ZMod 2) (moved τ A) = 3 :=
    fourDimensionalSource_moved_finrank τ A E hE c
  let L := A.map Y.subtype
  have hm : moved τ A = moved (fixedQuotient ρ Y) L := by
    have hh := subspaceCommutator_map_embedding τ (fixedQuotient ρ Y) Y.subtype
      (LinearMap.id : (V ⧸ fixedSpace ρ Y) →ₗ[ZMod 2] (V ⧸ fixedSpace ρ Y))
      (fun _ _ => rfl) A ⊤
    simpa only [Submodule.map_id] using hh
  obtain ⟨hs,hc,he,ho⟩ := source_linearThree_factor_structure T hP Y A hgen BinaryField.two
    (by decide) c.natural.groupEquiv
  let := hs
  let e := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans c.natural.groupEquiv
  obtain ⟨eg,f,hf⟩ := BinaryFullLinearRecognition.binary_three_moved_normalizer_natural
    (fixedQuotient ρ Y) L e (by
      change Module.finrank (ZMod 2) (moved (fixedQuotient ρ Y) L) = 3
      rw [← hm]
      exact hd)
  exact component_normalizer_not_natural_three T hP hc he ho
    (BinaryFullLinearRecognition.fullMovedNormalizerSpace (fixedQuotient ρ Y) L).toRepresentation
    BinaryField.two ⟨⟨eg,f,hf⟩⟩

/-- The exact remaining natural rank-one row, on the original quotient summand. -/
@[expose] def SourceRankOneFactor {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (A : Subgroup D) (U : Subrepresentation σ) : Prop :=
  U.toSubmodule = moved σ A ∧
    ((∃ F : BinaryField, IsLinearNatural
      (((fixed σ).quotientImage U).toRepresentation.comp A.subtype) F 2) ∨
      IsSymmetricNatural (((fixed σ).quotientImage U).toRepresentation.comp A.subtype) 5)

/-- Every original normal factor row is natural of rank one. -/
theorem source_normal_factor_rank_one
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (A : Subgroup Y) [A.Normal]
    (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (U : Subrepresentation (ρ.comp Y.subtype))
    (h : SourceInduction.SourceFactorCase (ρ.comp Y.subtype) A U) :
    SourceRankOneFactor (ρ.comp Y.subtype) A U := by
  have hr := source_normal_factor_rankOne_or_exceptional ρ T hP Y A hgen U h
  cases hr with
  | linearTwo hm F hn => exact ⟨hm,Or.inl ⟨F,hn⟩⟩
  | symmetricFive hm hn => exact ⟨hm,Or.inr hn⟩
  | exceptional hm c => exact (source_exceptional_four_factor_excluded ρ T hP Y A hgen U hm c).elim

/-- Both original summands have rank-one natural coordinates. -/
theorem source_two_factor_rank_one
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (c : SourceInduction.SourceTwoFactorCase (ρ.comp Y.subtype)) :
    SourceRankOneFactor (ρ.comp Y.subtype) c.first c.firstSpace ∧
      SourceRankOneFactor (ρ.comp Y.subtype) c.second c.secondSpace := by
  let := c.product.first_normal
  let := c.product.second_normal
  exact ⟨source_normal_factor_rank_one ρ T hP Y c.first hgen _ c.firstCase,
    source_normal_factor_rank_one ρ T hP Y c.second hgen _ c.secondCase⟩

/-- The original offender product has exactly the same two rank-one summands. -/
theorem source_offender_two_factor_rank_one
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (c : SourceInduction.SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype)) :
    SourceRankOneFactor (ρ.comp (offenderSubgroup ρ).subtype) c.first c.firstSpace ∧
      SourceRankOneFactor (ρ.comp (offenderSubgroup ρ).subtype) c.second c.secondSpace := by
  let := offenderSubgroup_normal ρ
  exact source_two_factor_rank_one ρ T hP _ (offender_generation T hP ρ hff hcore).2 c
end CFSG.Quasithin.ChapterB
