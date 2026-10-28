module
public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelFourDuality
public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelFourFieldRigidity

/-!
# Compatible whole-Borel coordinates from marked endpoint isomorphisms

Two arbitrary actual endpoints map isomorphically to the field-four line
endpoint, and their common subgroup maps to the whole Borel. If the two
radicals have the opposite ordered images, endpoint duality changes one
side to the point endpoint. The discrepancy between the Borel markings
preserves both ordered radical planes, so the proved full-Borel restriction
factorization corrects it. No compatibility hypothesis between the two
markings, independently chosen endpoint package, or mixed-product relation
is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Representation.SL2FourNatural
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.LinearAmbientGeometry Matrix.PSL3Even.UnipotentGeometry
open Theory.GroupTheory.RankTwoAmalgam
variable {G : Type*} [Group G]

private theorem middle_image (P J X : Subgroup G) (hJP : J≤P) (hXJ : X≤J)
    (f : P≃*lineLocal F) (j : J≃*borel F) (K : Subgroup (U F))
    (hf : (X.subgroupOf P).map ((lineLocal F).subtype.comp f.toMonoidHom)=K.map (projective F))
    (hc : ∀ x : J,f (inclusion hJP x)=lineBorelInclusion (j x)) :
    (X.subgroupOf J).map j.toMonoidHom=K.map (borelUnipotent F) := by
  have hi : (X.subgroupOf J).map (inclusion hJP)=X.subgroupOf P := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,hXJ hx⟩,hx,rfl⟩
  have he : (borel F).subtype.comp j.toMonoidHom=
      ((lineLocal F).subtype.comp f.toMonoidHom).comp (inclusion hJP) :=
    MonoidHom.ext (fun x => congrArg Subtype.val (hc x).symm)
  apply Subgroup.map_injective (borel F).subtype_injective
  rw [Subgroup.map_map,he,←Subgroup.map_map,hi,hf,Subgroup.map_map]
  rfl

/-- Opposite radical markings on the actual endpoint and whole-Borel
isomorphisms produce a compatible marking of the full amalgam. -/
theorem marked_borel_pair_iso
    (P₁ P₂ J A B : Subgroup G) (hJ₁ : J ≤ P₁) (hJ₂ : J ≤ P₂)
    (hAJ : A ≤ J) (hBJ : B ≤ J)
    (fA : P₁ ≃* lineLocal F) (fB : P₂ ≃* lineLocal F)
    (jA jB : J ≃* borel F)
    (hfAA : (A.subgroupOf P₁).map ((lineLocal F).subtype.comp fA.toMonoidHom) =
      projectivePlane₂ F)
    (hfAB : (B.subgroupOf P₁).map ((lineLocal F).subtype.comp fA.toMonoidHom) =
      projectivePlane₁ F)
    (hfBB : (B.subgroupOf P₂).map ((lineLocal F).subtype.comp fB.toMonoidHom) =
      projectivePlane₂ F)
    (hfBA : (A.subgroupOf P₂).map ((lineLocal F).subtype.comp fB.toMonoidHom) =
      projectivePlane₁ F)
    (hcA : ∀ x : J, fA (inclusion hJ₁ x) = lineBorelInclusion (jA x))
    (hcB : ∀ x : J, fB (inclusion hJ₂ x) = lineBorelInclusion (jB x)) :
    Nonempty (Iso (ofSubgroups P₁ J P₂ hJ₁ hJ₂) (fullBorelAmalgam F)) := by
  have hAA := middle_image P₁ J A hJ₁ hAJ fA jA (V₂ F) hfAA hcA
  have hAB' := middle_image P₁ J B hJ₁ hBJ fA jA (V₁ F) hfAB hcA
  have hBB := middle_image P₂ J B hJ₂ hBJ fB jB (V₂ F) hfBB hcB
  have hBA' := middle_image P₂ J A hJ₂ hAJ fB jB (V₁ F) hfBA hcB
  obtain ⟨δ,hδ,hδu⟩ := exists_borel_endpoint_duality
  let jL := jA.trans δ.symm
  let twist : MulAut (borel F) := jL.symm.trans jB
  have ht₁ (u : U F) (hu : u∈V₁ F) :
      twist (borelUnipotent F u)∈(V₁ F).map (borelUnipotent F) := by
    have hd : δ (borelUnipotent F u)∈(V₂ F).map (borelUnipotent F) := by
      rw [hδu]
      exact mem_map_of_mem _ ((mem_V₂ F _).mpr ((mem_V₁ F u).mp hu))
    rw [←hAA] at hd
    obtain ⟨x,hx,he⟩ := hd
    change jB (jA.symm (δ (borelUnipotent F u)))∈_
    rw [←he]
    change jB (jA.symm (jA x))∈_
    rw [MulEquiv.symm_apply_apply,←hBA']
    exact mem_map_of_mem _ hx
  have ht₂ (u : U F) (hu : u∈V₂ F) :
      twist (borelUnipotent F u)∈(V₂ F).map (borelUnipotent F) := by
    have hd : δ (borelUnipotent F u)∈(V₁ F).map (borelUnipotent F) := by
      rw [hδu]
      exact mem_map_of_mem _ ((mem_V₁ F _).mpr ((mem_V₂ F u).mp hu))
    rw [←hAB'] at hd
    obtain ⟨x,hx,he⟩ := hd
    change jB (jA.symm (δ (borelUnipotent F u)))∈_
    rw [←he]
    change jB (jA.symm (jA x))∈_
    rw [MulEquiv.symm_apply_apply,←hBB]
    exact mem_map_of_mem _ hx
  let e : Iso (ofSubgroups P₁ J P₂ hJ₁ hJ₂)
      (twistRight (fullBorelAmalgam F) twist) := {
    left := fA.trans (endpointDuality.symm.trans (MulEquiv.subgroupCongr field_four_parabolics.1.symm))
    middle := jL
    right := fB.trans (MulEquiv.subgroupCongr field_four_parabolics.2.symm)
    left_commutes := fun x => by
      apply Subtype.ext
      change (endpointDuality.symm (fA (inclusion hJ₁ x)) : PSL(3,F))=(jL x : PSL(3,F))
      have hh : endpointDuality.symm (fA (inclusion hJ₁ x))=pointBorelInclusion (jL x) := by
        apply endpointDuality.injective
        rw [MulEquiv.apply_symm_apply,hcA,hδ]
        change lineBorelInclusion (jA x)=lineBorelInclusion (δ (δ.symm (jA x)))
        rw [MulEquiv.apply_symm_apply]
      exact congrArg Subtype.val hh
    right_commutes := fun x => by
      apply Subtype.ext
      change (fB (inclusion hJ₂ x) : PSL(3,F))=(twist (jL x) : PSL(3,F))
      rw [hcB]
      change (jB x : PSL(3,F))=(jB (jL.symm (jL x)) : PSL(3,F))
      rw [MulEquiv.symm_apply_apply] }
  exact ⟨e.trans (full_borel_twist_factors F (by rw [Nat.card_eq_fintype_card,card_field])
    twist ht₁ ht₂).iso⟩


end Matrix.PSL3.SmallCompletion
