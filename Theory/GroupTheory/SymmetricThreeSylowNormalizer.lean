module
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.PResidual.SymmetricThreeProducts
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Sylow normalizers and odd residuals in the symmetric-three models

A Sylow two-subgroup of S₃×S₃ is the product of its two Sylow
projections. An element normalizing it therefore normalizes each
projection; the self-normalizer theorem in S₃ puts that element back in
the product. Transport through an actual group isomorphism gives the
same conclusion for either S₃ or S₃×S₃.

The two-residual embeds in a product of alternating triples and is a
three-group. Thus it meets the Sylow normalizer trivially. The final
transport keeps the normalizer in the original ambient group and the
literal inclusion-image of the residual. This is the local model input
for the intersection O²(I*)∩L₁*=1 in Aschbacher–Smith 13.4.8, printed p.905;
its actual centralizer application is in FixedCoreSource/Solvable/LocalProduct.
-/

public noncomputable section
open Subgroup
namespace SymmetricThreeSylowNormalizer
local notation "S3" => Equiv.Perm (Fin 3)

private theorem one_factor (P : Sylow 2 S3) : normalizer (P : Set S3) = P := by
  have hc : pCore 2 S3 = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id S3)
      Function.surjective_id (by
        simp only [MonoidHom.ker_id]
        exact IsPGroup.of_subsingleton 2 _)
    simpa only [MonoidHom.ker_id] using hh.symm
  exact SymmetricThreeTwoCore.sylow_self_normalizing
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot) P

private theorem two_factors (P : Sylow 2 (S3 × S3)) :
    normalizer (P : Set (S3 × S3)) = P := by
  let P₁ := P.mapSurjective (f := MonoidHom.fst S3 S3) (fun x => ⟨(x, 1), rfl⟩)
  let P₂ := P.mapSurjective (f := MonoidHom.snd S3 S3) (fun x => ⟨(1, x), rfl⟩)
  have hcard (Q : Sylow 2 S3) : Nat.card Q = 2 := by
    rw [Q.card_eq_multiplicity, Nat.card_perm, Nat.card_fin]
    decide +kernel
  have hprod : IsPGroup 2 ((P₁ : Subgroup S3).prod (P₂ : Subgroup S3)) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod, hcard, hcard]
    rfl
  have hPP : (P : Subgroup (S3 × S3)) ≤ (P₁ : Subgroup S3).prod (P₂ : Subgroup S3) := by
    intro x hx
    exact ⟨mem_map_of_mem (MonoidHom.fst S3 S3) hx,
      mem_map_of_mem (MonoidHom.snd S3 S3) hx⟩
  have he := P.is_maximal' hprod hPP
  apply le_antisymm _ le_normalizer
  intro x hx
  rw [← he]
  constructor
  · have hh := (P : Subgroup (S3 × S3)).le_normalizer_map (MonoidHom.fst S3 S3)
      (mem_map_of_mem (MonoidHom.fst S3 S3) hx)
    exact (one_factor P₁).le hh
  · have hh := (P : Subgroup (S3 × S3)).le_normalizer_map (MonoidHom.snd S3 S3)
      (mem_map_of_mem (MonoidHom.snd S3 S3) hx)
    exact (one_factor P₂).le hh

/-- Both source symmetric-three models have self-normalizing Sylow two-subgroups. -/
theorem of_models {D : Type*} [Group D] [Finite D]
    (hD : Nonempty (D ≃* S3) ∨ Nonempty (D ≃* (S3 × S3))) (P : Sylow 2 D) :
    normalizer (P : Set D) = P := by
  rcases hD with he | he
  · obtain ⟨e⟩ := he
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [P.normalizer_map_surjective e.toMonoidHom e.surjective]
    exact one_factor (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  · obtain ⟨e⟩ := he
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [P.normalizer_map_surjective e.toMonoidHom e.surjective]
    exact two_factors (P.mapSurjective (f := e.toMonoidHom) e.surjective)

/-- The actual two-residual in either model is a three-group. -/
theorem residual_threeGroup_of_models {D : Type*} [Group D]
    (hD : Nonempty (D ≃* S3) ∨ Nonempty (D ≃* (S3 × S3))) :
    IsPGroup 3 (pResidual 2 D) := by
  let f : (S3 × S3) →* (Fin 2 → S3) := {
    toFun := (finTwoArrowEquiv S3).symm
    map_one' := by ext i; fin_cases i <;> rfl
    map_mul' := fun x y => by ext i; fin_cases i <;> rfl }
  have hf : Function.Injective f := (finTwoArrowEquiv S3).symm.injective
  rcases hD with he | he
  · obtain ⟨e⟩ := he
    let g : D →* (S3 × S3) := e.toMonoidHom.prod (1 : D →* S3)
    exact Theory.GroupTheory.pResidual_threeGroup_of_injective_permThree_product (f.comp g)
      (hf.comp (fun a b h => e.injective (congrArg Prod.fst h)))
  · obtain ⟨e⟩ := he
    exact Theory.GroupTheory.pResidual_threeGroup_of_injective_permThree_product
      (f.comp e.toMonoidHom) (hf.comp e.injective)

/-- An element of the odd residual normalizing the original Sylow is trivial. -/
theorem residual_disjoint_normalizer {D : Type*} [Group D] [Finite D]
    (hD : Nonempty (D ≃* S3) ∨ Nonempty (D ≃* (S3 × S3))) (P : Sylow 2 D) :
    Disjoint (pResidual 2 D) (normalizer (P : Set D)) := by
  rw [of_models hD P]
  exact (residual_threeGroup_of_models hD).disjoint_of_coprime P.isPGroup' (by decide)

/-- The intrinsic residual assertion retains the ambient normalizer of the
given subgroup, rather than replacing it by a normalizer inside the model. -/
theorem residual_image_disjoint_normalizer {G : Type*} [Group G] [Finite G]
    (I J : Subgroup G)
    (hI : Nonempty (I ≃* S3) ∨ Nonempty (I ≃* (S3 × S3)))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = J) :
    Disjoint ((pResidual 2 I).map I.subtype) (normalizer (J : Set G)) := by
  have hJI : J ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  have hJP : J.subgroupOf I = (P : Subgroup I) := by
    rw [← hP]
    ext x
    exact mem_map_iff_mem I.subtype_injective
  have hd := residual_disjoint_normalizer hI P
  rw [disjoint_def] at hd ⊢
  rintro x ⟨a, ha, rfl⟩ hn
  have hna : a ∈ normalizer (P : Set I) := by
    change a ∈ normalizer ((P : Subgroup I) : Set I)
    rw [← hJP, ← subgroupOf_normalizer_eq hJI]
    exact hn
  exact congrArg Subtype.val (hd ha hna)

end SymmetricThreeSylowNormalizer
