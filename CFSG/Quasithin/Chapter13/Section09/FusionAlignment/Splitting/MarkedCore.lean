module
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Splitting.Normalizer
public import Theory.SpecificGroups.BinaryFiveAffine.Marking
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Alignment
public import Theory.GroupTheory.PCoreImage
/-!
# The original split retains its Klein four-group and fusion

The literal affine equivalence transports O₂(X) through the same injective
homomorphism used for the factors. The native last-three subgroup lies in
B, and its nonidentity elements are conjugate to the original marked t.
Source: Aschbacher–Smith 13.9.10, printed p.973.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup FusionAlignment
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

/-- The marked affine equivalence preserves the entire original centralizer. -/
theorem exists_marked_centralizer_split_with_core {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    ∃(R X:Subgroup G) (split:normalizerCentralizer m.B m.t≃*R×X)
      (eR:DihedralGroup 4≃*R) (_eX:Equiv.Perm (Fin 4)≃*X),
      (∀c:normalizerCentralizer m.B m.t,(c:G)=((split c).1:G)*((split c).2:G)) ∧
      R≤normalizerCentralizer m.B m.t ∧ X≤normalizerCentralizer m.B m.t ∧
      R≤centralizer (X:Set G) ∧ Disjoint R X ∧ (eR (.r 2):G)=m.t ∧
      X.pCoreIn 2≤m.B ∧ (∀x∈X.pCoreIn 2,x≠1→IsConj m.t x) := by
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
  have hcore : X.pCoreIn 2=(BinaryFiveAffine.X.pCoreIn 2).map φ :=
    (Subgroup.map_pCoreIn_of_ker_isPGroup φ (IsPGroup.ker_isPGroup_of_injective hφ)
      BinaryFiveAffine.X).symm
  have hVB : BinaryFiveAffine.vectorGroup.map φ=m.B := by
    rw [←map_map,heB,map_subgroupOf_eq_of_le m.B.le_normalizer]
  refine ⟨R,X,split,eR,eX,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · rw [hcore,←hVB]
    apply map_mono
    change (pCore 2 BinaryFiveAffine.X).map BinaryFiveAffine.X.subtype≤_
    rw [BinaryFiveAffine.X_twoCore_image]
    exact map_le_range _ _
  · intro x hx hne
    rw [hcore] at hx
    obtain ⟨y,⟨y₀,hy₀,rfl⟩,rfl⟩:=hx
    have hyne : y₀≠1 := by
      intro he
      apply hne
      rw [he,map_one,map_one]
    obtain ⟨g,hg⟩:=BinaryFiveAffine.X_twoCore_conjugate y₀ hy₀ hyne
    apply isConj_iff.mpr
    refine ⟨φ g,?_⟩
    rw [←hφt,←map_inv,←map_mul,←map_mul,hg]
    rfl

end CFSG.Quasithin.Chapter13.Section09.Marking
