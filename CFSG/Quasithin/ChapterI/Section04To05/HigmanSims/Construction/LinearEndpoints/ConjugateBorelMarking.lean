module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.OriginalBorelPair
public import Theory.SpecificGroups.PSL3.SmallCompletion.MarkedBorelPair
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.OriginalBorelPair

/-!
# Compatible whole-Borel marking for the literal conjugate endpoint pair

The second endpoint and its entire intersection marking are transported
through the same original conjugation that swaps the radicals. The proved
native whole-Borel factorization aligns the two markings. Canonical field
transport retains both actual endpoint two-cores.

The internal import reuses only the frozen canonical field-transport
isomorphism; no second natural-endpoint package is assumed or constructed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.HigmanSims
open Representation.SL2FourNatural Representation.SL2FourNatural.BorelFactors
open Matrix.PSL3.LinearThree Matrix.PSL3.SmallCompletion
variable {G : Type*} [Group G]

private theorem conjugate_subgroupOf_map (P X Y : Subgroup G)
    (α : MulAut G) (hY : Y=X.map α.toMonoidHom) :
    let k := P.equivMapOfInjective α.toMonoidHom α.injective
    (Y.subgroupOf (P.map α.toMonoidHom)).map k.symm.toMonoidHom=X.subgroupOf P := by
  let k := P.equivMapOfInjective α.toMonoidHom α.injective
  ext x
  rw [mem_map_equiv]
  change α (x : G)∈Y ↔ (x : G)∈X
  rw [hY]
  exact mem_map_iff_mem α.injective

/-- The specified original endpoint and its literal conjugate admit a
compatible canonical flag marking on their whole intersection, with both
original radicals mapped to the entire endpoint two-cores. -/
theorem NaturalEndpointData.conjugate_borel_marking {A B : Subgroup G}
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (d : NaturalEndpointData A) (hB16 : Nat.card B=16)
    (hBP : B≤d.carrier) (hBA : B≤normalizer (A : Set G))
    (hR : U0.map d.embedding = ((d.symplectic_quotient.toMonoidHom.comp
      (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))))).comp (inclusion hBA)).range)
    (c : G) (hBc : B=A.map (MulAut.conj c).toMonoidHom)
    (hAc : A=B.map (MulAut.conj c).toMonoidHom)
    (hJ192 : Nat.card (d.carrier⊓d.carrier.map (MulAut.conj c).toMonoidHom : Subgroup G)=192)
    (hcJ : c∈normalizer ((d.carrier⊓d.carrier.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G)) :
    let P₂ := d.carrier.map (MulAut.conj c).toMonoidHom
    ∃ marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups d.carrier (d.carrier⊓P₂) P₂ inf_le_left inf_le_right)
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam Matrix.PSL3Four.F),
      (A.subgroupOf d.carrier).map marking.left.toMonoidHom=
        pCore 2 (pointParabolic Matrix.PSL3Four.F) ∧
      (B.subgroupOf P₂).map marking.right.toMonoidHom=
        pCore 2 (lineParabolic Matrix.PSL3Four.F) := by
  let α := MulAut.conj c
  let P₂ := d.carrier.map α.toMonoidHom
  let J := d.carrier⊓P₂
  have hAP₂ : A≤P₂ := by rw [hAc]; exact map_mono hBP
  have hBP₂ : B≤P₂ := by rw [hBc]; exact map_mono d.kernel_le
  have hP₂N : P₂≤normalizer (B : Set G) := by
    have hh := map_mono (f:=α.toMonoidHom) d.normalizes
    rw [map_equiv_normalizer_eq,←hBc] at hh
    exact hh
  have hAJ : A≤J := le_inf d.kernel_le hAP₂
  have hBJ : B≤J := le_inf hBP hBP₂
  obtain ⟨fA,jA,_,_,hfAA,hfAB,hcA⟩ := d.exists_whole_borel_marking B hB16 hBP hBA hR
    J inf_le_left (inf_le_right.trans hP₂N) hJ192
  let k : d.carrier ≃* P₂ := d.carrier.equivMapOfInjective α.toMonoidHom α.injective
  let kJ : MulAut J := J.normalizerMonoidHom ⟨c,hcJ⟩
  let fB := k.symm.trans fA
  let jB := kJ.symm.trans jA
  have hkA : (B.subgroupOf P₂).map k.symm.toMonoidHom=A.subgroupOf d.carrier :=
    conjugate_subgroupOf_map d.carrier A B α hBc
  have hkB : (A.subgroupOf P₂).map k.symm.toMonoidHom=B.subgroupOf d.carrier :=
    conjugate_subgroupOf_map d.carrier B A α hAc
  have hfBB : (B.subgroupOf P₂).map ((lineLocal F).subtype.comp fB.toMonoidHom)=
      Matrix.PSL3Even.UnipotentGeometry.projectivePlane₂ F := by
    change (B.subgroupOf P₂).map
      (((lineLocal F).subtype.comp fA.toMonoidHom).comp k.symm.toMonoidHom)=_
    rw [←Subgroup.map_map,hkA,hfAA]
  have hfBA : (A.subgroupOf P₂).map ((lineLocal F).subtype.comp fB.toMonoidHom)=
      Matrix.PSL3Even.UnipotentGeometry.projectivePlane₁ F := by
    change (A.subgroupOf P₂).map
      (((lineLocal F).subtype.comp fA.toMonoidHom).comp k.symm.toMonoidHom)=_
    rw [←Subgroup.map_map,hkB,hfAB]
  have hkJ (x : J) : k (inclusion inf_le_left x)=inclusion inf_le_right (kJ x) :=
    Subtype.ext rfl
  have hcB (x : J) : fB (inclusion inf_le_right x)=lineBorelInclusion (jB x) := by
    have he := congrArg k.symm (hkJ (kJ.symm x))
    rw [k.symm_apply_apply,kJ.apply_symm_apply] at he
    change fA (k.symm (inclusion inf_le_right x))=lineBorelInclusion (jA (kJ.symm x))
    rw [←he]
    exact hcA (kJ.symm x)
  obtain ⟨e⟩ := marked_borel_pair_iso d.carrier P₂ J A B inf_le_left inf_le_right
    hAJ hBJ fA fB jA jB hfAA hfAB hfBB hfBA hcA hcB
  let marking := e.trans canonical_flag_iso
  have hcoreA : A.subgroupOf d.carrier=pCore 2 d.carrier := by
    obtain ⟨f,_,_,hf,_⟩ := d.exists_affine_marking
    apply Subgroup.map_injective (f:=f.toMonoidHom) f.injective
    rw [hf,pCore_map_iso,Matrix.SL2.affine_twoCore_eq]
  have hcoreB : B.subgroupOf P₂=pCore 2 P₂ := by
    apply Subgroup.map_injective (f:=k.symm.toMonoidHom) k.symm.injective
    rw [hkA,pCore_map_iso,hcoreA]
  refine ⟨marking,?_,?_⟩
  · rw [hcoreA,pCore_map_iso]
  · rw [hcoreB,pCore_map_iso]

end CFSG.Quasithin.HigmanSims
