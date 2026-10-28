module
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Splitting.Normalizer
public import Theory.SpecificGroups.BinaryFiveAffine.Marking
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Alignment
/-!
# Transporting the marked D₈ × S₄ split to the source configuration

The checked affine five-point equivalence identifies the native involution
centralizer with the literal `N_G(B) ∩ C_G(t)`. Mapping the native factors
through this equivalence gives actual subgroups of G, exact multiplication
coordinates, disjointness and centralization, and preserves the marked t.
This is the source-facing input for Lemma 13.9.10.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup FusionAlignment
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

/-- The marked affine equivalence preserves the entire original centralizer. -/
theorem exists_marked_centralizer_split {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    ∃(R X:Subgroup G) (split:normalizerCentralizer m.B m.t≃*R×X)
      (eR:DihedralGroup 4≃*R) (_eX:Equiv.Perm (Fin 4)≃*X),
      (∀c:normalizerCentralizer m.B m.t,(c:G)=((split c).1:G)*((split c).2:G)) ∧
      R≤normalizerCentralizer m.B m.t ∧ X≤normalizerCentralizer m.B m.t ∧
      R≤centralizer (X:Set G) ∧ Disjoint R X ∧ (eR (.r 2):G)=m.t := by
  obtain ⟨e,heT,heB⟩:=m.exists_binary_five_normalizer hG
  let K := normalizer (m.B:Set G)
  let φ : BinaryFiveAffine.W→*G := K.subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hφt : φ BinaryFiveAffine.t=m.t := heT
  have hc : BinaryFiveAffine.centralizer.map φ=normalizerCentralizer m.B m.t := by
    ext x
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨(e w).property,mem_centralizer_singleton_iff.mpr ?_⟩
      rw [←hφt,←map_mul,←map_mul]
      exact congrArg φ (mem_centralizer_singleton_iff.mp hw)
    · rintro ⟨hx,hxt⟩
      obtain ⟨w,hw⟩:=e.surjective ⟨x,hx⟩
      have hw' : φ w=x := congrArg Subtype.val hw
      refine ⟨w,mem_centralizer_singleton_iff.mpr ?_,hw'⟩
      apply hφ
      rw [map_mul,map_mul,hφt,hw']
      exact mem_centralizer_singleton_iff.mp hxt
  let eC : BinaryFiveAffine.centralizer≃*normalizerCentralizer m.B m.t :=
    (Subgroup.equivMapOfInjective _ φ hφ).trans (MulEquiv.subgroupCongr hc)
  let R := BinaryFiveAffine.R.map φ
  let X := BinaryFiveAffine.X.map φ
  let eRm : BinaryFiveAffine.R≃*R := Subgroup.equivMapOfInjective _ φ hφ
  let eXm : BinaryFiveAffine.X≃*X := Subgroup.equivMapOfInjective _ φ hφ
  let split := eC.symm.trans (BinaryFiveAffine.split.trans (eRm.prodCongr eXm))
  let eR := BinaryFiveAffine.dihedralEquiv.trans eRm
  let eX := BinaryFiveAffine.symmetricEquiv.trans eXm
  refine ⟨R,X,split,eR,eX,?_,?_,?_,?_,?_,?_⟩
  · intro c
    obtain ⟨w,rfl⟩:=eC.surjective c
    change φ w.val=φ (BinaryFiveAffine.split (eC.symm (eC w))).1.val *
      φ (BinaryFiveAffine.split (eC.symm (eC w))).2.val
    rw [eC.symm_apply_apply,←map_mul,BinaryFiveAffine.split_coordinates]
  · exact (map_mono BinaryFiveAffine.R_le_centralizer).trans hc.le
  · exact (map_mono BinaryFiveAffine.X_le_centralizer).trans hc.le
  · rintro _ ⟨a,ha,rfl⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨b,hb,rfl⟩
    rw [←map_mul,←map_mul]
    exact congrArg φ (mem_centralizer_iff.mp (BinaryFiveAffine.R_centralizes_X ha) _ hb)
  · apply disjoint_def.mpr
    rintro _ ⟨a,ha,rfl⟩ ⟨b,hb,he⟩
    have hab := hφ he
    subst b
    rw [disjoint_def.mp BinaryFiveAffine.disjoint_factors ha hb,map_one]
  · change φ (BinaryFiveAffine.dihedralEmbedding (.r 2))=m.t
    rw [BinaryFiveAffine.dihedral_marked,hφt]

end CFSG.Quasithin.Chapter13.Section09.Marking
