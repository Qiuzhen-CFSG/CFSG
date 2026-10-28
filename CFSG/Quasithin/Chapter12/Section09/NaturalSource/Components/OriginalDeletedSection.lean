module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalDeletedFourActor
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.BinaryConjugationCoordinates.FixedIndex
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# The actual fixed-index obstruction on a central quotient

A surjective conjugation section of an original elementary subgroup cannot
be the deleted A₈ module if the original actor has fixed index four and its
marked image is an elementary four-group. Fixed codimension decreases under
the actual quotient map, so central attachments in the original subgroup
are retained throughout.
Source application: Aschbacher--Smith 12.9.4, printed p.860.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W]
  {H I D : Subgroup G} [IsElementaryAbelian 2 I]

/-- The original fixed index four excludes a faithful elementary-four image
on any marked deleted-eight quotient of the original subgroup. -/
theorem deleted_eight_section_false_of_index_four
    (hHI : H ≤ normalizer (I : Set G)) (hDH : D ≤ H)
    (ρ : Representation (ZMod 2) H W) (p : I →* Multiplicative W)
    (hp : Function.Surjective p)
    (he : ∀ (a : H) (v : I),
      ρ a (p v).toAdd = (p (I.normalizerMonoidHom (inclusion hHI a) v)).toAdd)
    (q : H →* alternatingGroup (Fin 8))
    (E : W ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hE : ∀ a w, E (ρ a w) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (q a) (E w))
    (hcard : Nat.card ((D.subgroupOf H).map q) = 4)
    (hsq : ∀ a ∈ (D.subgroupOf H).map q, a ^ 2 = 1)
    (hindex : (I ⊓ centralizer (D : Set G)).relIndex I = 4) : False := by
  let τ := BinaryConjugationSection.originalNormalizerAction hHI
  let f : Additive I →ₗ[ZMod 2] W := p.toAdditiveLeft.toZModLinearMap 2
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨v, hv⟩ := hp (Multiplicative.ofAdd w)
    exact ⟨Additive.ofMul v, congrArg Multiplicative.toAdd hv⟩
  have hfe : ∀ a v, f (τ a v) = ρ a (f v) := by
    intro a v
    change (p ((τ a v).toMul)).toAdd = _
    rw [BinaryConjugationSection.originalNormalizerAction_apply]
    exact (he a v.toMul).symm
  have hle := fixedCodim_le_of_equivariant_surjection τ ρ f hf hfe (D.subgroupOf H)
  let eI : I ≃* Multiplicative (Additive I) := {
    toFun v := Multiplicative.ofAdd (Additive.ofMul v)
    invFun v := v.toAdd.toMul
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hrange : (inclusion hDH).range = D.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact d.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hi := BinaryConjugationCoordinates.model_fixed_index D I
    (hDH.trans hHI) τ (inclusion hDH) eI (by
      intro d v
      apply Additive.toMul.injective
      exact (BinaryConjugationSection.originalNormalizerAction_apply hHI
        (inclusion hDH d) (Additive.ofMul v)).symm)
  rw [hrange, ← inf_relIndex_left, hindex] at hi
  have hd : fixedCodim τ (D.subgroupOf H) = 2 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    exact hi.symm
  let j : H →* Equiv.Perm (Fin 8) := (alternatingGroup (Fin 8)).subtype.comp q
  let A := (D.subgroupOf H).map j
  have hmap : A = ((D.subgroupOf H).map q).map (alternatingGroup (Fin 8)).subtype :=
    (map_map _ _ _).symm
  have hA : A ≤ alternatingGroup (Fin 8) := by
    rw [hmap]
    exact map_subtype_le _
  have hAsq : ∀ a ∈ A, a ^ 2 = 1 := by
    rw [hmap]
    rintro a ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hsq b hb)
  have hAc : Nat.card A = 4 := by
    rw [hmap, card_map_of_injective (alternatingGroup (Fin 8)).subtype_injective, hcard]
  have hcod := fixedCodim_map_equivariant ρ (BinaryPermutation.naturalRepresentation (Fin 8))
    j E hE (D.subgroupOf H)
  have hgt := deleted_eight_four_fixedCodim_gt_two A hA hAsq hAc
  change fixedCodim ρ (D.subgroupOf H) =
    fixedCodim (BinaryPermutation.naturalRepresentation (Fin 8)) A at hcod
  omega

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
