module
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.WholeBorelMarking
public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelFourDuality
public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelFourFieldRigidity

/-! The two actual endpoint markings agree after the proved native whole-Borel
correction. The original endpoint carriers and literal intersection inclusions
are retained throughout. -/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.HigmanSims
open Representation.SL2FourNatural Representation.SL2FourNatural.BorelFactors
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearAmbientGeometry Matrix.PSL3Even.UnipotentGeometry Theory.GroupTheory.RankTwoAmalgam
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

/-- The unchanged original endpoints admit compatible markings on their
whole literal intersection. All marking hypotheses are source-produced
natural endpoint data and exact opposite root images. -/
theorem NaturalEndpointData.compatible_borel_marking
    {A B : Subgroup G} [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (dA : NaturalEndpointData A) (dB : NaturalEndpointData B)
    (hA16 : Nat.card A=16) (hB16 : Nat.card B=16)
    (hAB : A≤normalizer (B : Set G)) (hBA : B≤normalizer (A : Set G))
    (hBP : B≤dA.carrier) (hAP : A≤dB.carrier)
    (hRA : U0.map dA.embedding = ((dA.symplectic_quotient.toMonoidHom.comp
      (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))))).comp (inclusion hBA)).range)
    (hRB : U0.map dB.embedding = ((dB.symplectic_quotient.toMonoidHom.comp
      (QuotientGroup.mk' (B.subgroupOf (normalizer (B : Set G))))).comp (inclusion hAB)).range)
    (hJ192 : Nat.card (dA.carrier⊓dB.carrier : Subgroup G)=192) :
    Nonempty (Iso (ofSubgroups dA.carrier (dA.carrier⊓dB.carrier) dB.carrier inf_le_left inf_le_right)
      (fullBorelAmalgam F)) := by
  let J := dA.carrier⊓dB.carrier
  have hAJ : A≤J := le_inf dA.kernel_le hAP
  have hBJ : B≤J := le_inf hBP dB.kernel_le
  obtain ⟨fA,jA,_,_,hfAA,hfAB,hcA⟩ := dA.exists_whole_borel_marking B hB16 hBP hBA hRA
    J inf_le_left (inf_le_right.trans dB.normalizes) hJ192
  obtain ⟨fB,jB,_,_,hfBB,hfBA,hcB⟩ := dB.exists_whole_borel_marking A hA16 hAP hAB hRB
    J inf_le_right (inf_le_left.trans dA.normalizes) hJ192
  have hAA := middle_image dA.carrier J A inf_le_left hAJ fA jA (V₂ F) hfAA hcA
  have hAB' := middle_image dA.carrier J B inf_le_left hBJ fA jA (V₁ F) hfAB hcA
  have hBB := middle_image dB.carrier J B inf_le_right hBJ fB jB (V₂ F) hfBB hcB
  have hBA' := middle_image dB.carrier J A inf_le_right hAJ fB jB (V₁ F) hfBA hcB
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
  let e : Iso (ofSubgroups dA.carrier J dB.carrier inf_le_left inf_le_right)
      (twistRight (fullBorelAmalgam F) twist) := {
    left := fA.trans (endpointDuality.symm.trans (MulEquiv.subgroupCongr field_four_parabolics.1.symm))
    middle := jL
    right := fB.trans (MulEquiv.subgroupCongr field_four_parabolics.2.symm)
    left_commutes := fun x => by
      apply Subtype.ext
      change (endpointDuality.symm (fA (inclusion inf_le_left x)) : PSL(3,F))=(jL x : PSL(3,F))
      have hh : endpointDuality.symm (fA (inclusion inf_le_left x))=pointBorelInclusion (jL x) := by
        apply endpointDuality.injective
        rw [MulEquiv.apply_symm_apply,hcA,hδ]
        change lineBorelInclusion (jA x)=lineBorelInclusion (δ (δ.symm (jA x)))
        rw [MulEquiv.apply_symm_apply]
      exact congrArg Subtype.val hh
    right_commutes := fun x => by
      apply Subtype.ext
      change (fB (inclusion inf_le_right x) : PSL(3,F))=(twist (jL x) : PSL(3,F))
      rw [hcB]
      change (jB x : PSL(3,F))=(jB (jL.symm (jL x)) : PSL(3,F))
      rw [MulEquiv.symm_apply_apply] }
  exact ⟨e.trans (full_borel_twist_factors F (by rw [Nat.card_eq_fintype_card,card_field])
    twist ht₁ ht₂).iso⟩

end CFSG.Quasithin.HigmanSims
