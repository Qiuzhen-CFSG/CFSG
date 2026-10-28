module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointSections
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourSection
public import Theory.GroupTheory.TwoFixedLinesIrreducible
public import Theory.GroupTheory.TransvectionDualIrreducible
public import Theory.Representation.HermitianTensorThree.PointSection.Crossing

/-!
# The selected-plane crossing and full point-core dual interval

The actual point radical gives coordinates on V_z=[V,O₂(L_z)]. A conjugate
of V_z in the selected pair core crosses U=A∩O₂(LT), forcing its original
C_G(z)-normal closure E outside O₂(LT). The central denominator stays ⟨z⟩.

The full transvection pairing also transfers irreducibility from V_z/⟨z⟩
to O₂(L_z)/V. Its actual kernel is V, and the annihilator argument allows the
natural and dual quotient maps to have been constructed independently.

Source: Aschbacher–Smith 8.2.11(4) and 8.2.12, printed p.722,
refs/quasithin.pdf. The Chapter 12 application discharges the crossing and
kernel premises for the literal tensor action. Identifying the full local
core image and completing the extraspecial closure remain subsequent steps.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

/-- Coordinates on the original residual commutator retain the complete point-core image. -/
theorem marked_point_residual_coordinates
    (V L : Subgroup G) [IsElementaryAbelian 2 V]
    (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1) (q : L →* binaryImage 1)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (z : V) (hz : e (Additive.ofMul z) = PointSection.pointVector) :
    ∀ v : Additive V, (v.toMul : G) ∈ Centralizer.commutatorSpace L V z ↔
      e v ∈ PointSection.moved := by
  let f := nativeBinaryEquiv.symm.toMonoidHom.comp q
  have hf : Function.Surjective f := nativeBinaryEquiv.symm.surjective.comp hq
  have hfk : IsPGroup 2 f.ker := by
    rwa [MonoidHom.ker_comp_of_injective _ _ nativeBinaryEquiv.symm.injective]
  have hP := marked_point_centralizer_preimage V L hLN e q he z hz
  have hXimage := (point_residual_images L (z : G) f hf hfk hP).2
  let X := Centralizer.localTwoCore L z
  have hXL : X ≤ L := (Centralizer.localTwoCore_le L z).trans
    ((Centralizer.localResidual_le L z).trans inf_le_left)
  let r := (binaryImage 1).subtype.comp (q.comp (inclusion hXL))
  have hRange : r.range = UnipotentRadicals.point 1 := by
    have hm := congrArg (Subgroup.map ((binaryImage 1).subtype.comp nativeBinaryEquiv.toMonoidHom)) hXimage
    rw [map_map,native_point_root_image] at hm
    have heq : ((binaryImage 1).subtype.comp nativeBinaryEquiv.toMonoidHom).comp f =
        (binaryImage 1).subtype.comp q := by
      apply MonoidHom.ext
      intro l
      exact congrArg Subtype.val (nativeBinaryEquiv.apply_symm_apply (q l))
    rw [heq] at hm
    have hi : (inclusion hXL).range = X.subgroupOf L := by
      ext l
      constructor
      · rintro ⟨x,rfl⟩
        exact x.property
      · intro hl
        exact ⟨⟨l,hl⟩,Subtype.ext rfl⟩
    change (((binaryImage 1).subtype.comp q).comp (inclusion hXL)).range = _
    rw [MonoidHom.range_comp,hi]
    exact hm
  exact marked_point_commutator_coordinates V X (hXL.trans hLN) e r
    (fun x v => he (inclusion hXL x) v) hRange

/-- The literal selected pair moves the original point five-space across
O₂(LT). Only the original relative normal closure in C_G(z) is used. -/
theorem selected_point_closure_crossing
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    {H M I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T M V I 1 i S) (hT : HypothesisE322 V T)
    (L Q : Subgroup G) (z : V)
    (hLN : L ≤ normalizer (V : Set G)) (hVQ : V ≤ Q)
    (hQC : Q ≤ centralizer (V : Set G))
    (hUeq : V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hzU : (z : G) ∈ V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G))
    (hWB : Centralizer.commutatorSpace L V z ≤ V ⊓ I.pCoreIn 2)
    (hnot : ¬ Centralizer.commutatorSpace L V z ≤ V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)) :
    ¬ (Centralizer.sourceClosure L V z).map
      (centralizer ({(z : G)} : Set G)).subtype ≤ Q := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let U := V ⊓ centralizer (A : Set G)
  obtain ⟨_,_,_,hker,_⟩ := selected_core_actor_data s hT
  have hAU : A ⊓ centralizer (V : Set G) = U := hker.trans hUeq.symm
  have hUA : U ≤ A := hAU.ge.trans inf_le_left
  have hcap : A ⊓ Q = U := le_antisymm
    ((inf_le_inf_left A hQC).trans hAU.le) (le_inf hUA (inf_le_left.trans hVQ))
  have hIC : I ≤ centralizer (U : Set G) := by
    have heU : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom := hUeq
    rw [heU]
    let : IsElementaryAbelian 2 (V.map (MulAut.conj i.val⁻¹).toMonoidHom) :=
      IsElementaryAbelian.map _
    exact s.generate.symm.le.trans (sup_le_centralizer_inf_of_abelian _ _)
  have hIP : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hconj : (Centralizer.commutatorSpace L V z).map
      (MulAut.conj i.val⁻¹).toMonoidHom ≤ A := by
    rintro _ ⟨v,hv,rfl⟩
    exact ⟨mem_map_of_mem _ (hWB hv).1,
      (mem_normalizer_iff.mp (hIP (I.inv_mem i.property)) v).mp (hWB hv).2⟩
  exact Centralizer.sourceClosure_not_le_of_crossing L V U A Q (z : G) i.val⁻¹
    z.property hzU hLN (hIC (I.inv_mem i.property)) hcap hconj hnot

omit [Finite G] in
/-- The original residual acts irreducibly on the full point-core quotient.
Its denominator is the entire original module, identified with the action kernel. -/
theorem point_residual_dual_interval
    (L V : Subgroup G) (z : G) (hz : z ≠ 1)
    (hZW : zpowers z ≤ Centralizer.commutatorSpace L V z)
    (hsections : PointSectionActions V (Centralizer.commutatorSpace L V z) (zpowers z)
      (Centralizer.localResidual L z))
    (htrans : FullPointTransvectionAction V (Centralizer.localTwoCore L z) z)
    (hker : (centralizer (V : Set G)).subgroupOf (Centralizer.localTwoCore L z) =
      V.subgroupOf (Centralizer.localTwoCore L z))
    (Y : Subgroup G) (hVY : V ≤ Y) (hYX : Y ≤ Centralizer.localTwoCore L z)
    (hRY : Centralizer.localResidual L z ≤ normalizer (Y : Set G)) :
    Y = V ∨ Y = Centralizer.localTwoCore L z := by
  obtain ⟨qW,hqW,hkerW,qX,_,hkerX,hpair⟩ := htrans
  have hRW : Centralizer.localResidual L z ≤
      normalizer (Centralizer.commutatorSpace L V z : Set G) := by
    obtain ⟨_,hRW,_⟩ := hsections
    exact hRW
  exact transvection_dual_interval (Centralizer.commutatorSpace L V z)
    (Centralizer.localTwoCore L z) V (Centralizer.localResidual L z) z hz
    qW hqW hkerW qX (hkerX.trans hker) hpair hZW
    ((Centralizer.localTwoCore_le L z).trans ((Centralizer.localResidual_le L z).trans inf_le_right))
    hRW (fun A => hsections.natural_interval _ _ _ _ A) Y hVY hYX hRY

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
