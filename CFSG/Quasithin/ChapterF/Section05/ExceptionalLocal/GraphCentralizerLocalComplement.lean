module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerKernel
public import CFSG.Quasithin.ChapterF.Section05.ModelVertexComplement
import all CFSG.Quasithin.ChapterF.Section05.ModelVertexComplement
import all CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointsPlane

/-!
# The corrected plane complement lies in the graph residual product

The first plane transposition multiplied by the marked short involution is
an explicit element of the common dihedral group U. Every other generating
transposition differs from it by an element of A₄, hence of O²(C_G(f)).
Consequently each parity-corrected local generator belongs to O²(C_G(f))⟨f⟩.
The actual R₀ therefore centralizes this entire marked complement.

This supplies the literal action mark needed for F.5.7 local-map agreement;
no abstract automorphism choice or additional C₄ hypothesis is used.
Source: Aschbacher–Smith F.5.5 and F.5.7, printed pp.301–303.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "S4" => Equiv.Perm (Fin 4)
local notation "C2" => Multiplicative (ZMod 2)
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)

omit [Finite G] in
private theorem plane_swap_short (hi:Function.Injective i) :
    sourceEndpointCoreMap c i hi true (Equiv.swap 0 1)*sourceMarkedShort c i=
      ResidualJoinModel.sourceHom c i (.sr 2) := by
  let u:planeParabolicSU F (form F σ hσ):=
    (EndpointPlane.graphFixedPlaneEquivProduct.symm (1,Equiv.swap (0:Fin 4) 1)).val
  let v:planeParabolicSU F (form F σ hσ):=⟨unipotentSU F σ hσ (shortParameter F σ),
    local_le_planeParabolic F (form F σ hσ) (unipotentSU_mem_local F σ hσ _)⟩
  let p:=((planeParabolicSU F (form F σ hσ)).equivMapOfInjective
    (projection 1 hn) (projection_injective 1 hn))
  have hu : sourceEndpointCoreMap c i hi true (Equiv.swap 0 1)=ordinaryMap c i true (p u) := by
    simp only [sourceEndpointCoreMap,source_Dendpoint_equiv_true,MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom,MonoidHom.inr_apply,Subgroup.coe_subtype]
    exact source_D_plane_equiv_symm_val c i hi (1,Equiv.swap 0 1)
  have hv : sourceMarkedShort c i=ordinaryMap c i true (p v) := by
    unfold sourceMarkedShort sourcePlaneParameter
    apply congrArg (ordinaryMap c i true)
    apply Subtype.ext
    rfl
  calc
    _ = ordinaryMap c i true (p u)*ordinaryMap c i true (p v) := congrArg₂ (·*·) hu hv
    _ = ordinaryMap c i true (p (u*v)) :=
      (((ordinaryMap c i true).comp p.toMonoidHom).map_mul u v).symm
    _ = ResidualJoinModel.sourceHom c i (.sr 2) := by
      apply sourceHom_eq_plane c i (.sr 2) (u*v)
      apply Subtype.ext
      apply Units.ext
      change (EndpointPlane.binaryMatrix (1,Equiv.swap (0:Fin 4) 1)).map EndpointPlane.binaryCast *
        unipotentMatrix F (shortParameter F σ).val=
        (ResidualJoinModel.binaryMatrix (.sr 2)).map ResidualJoinModel.binaryCast
      have hb : EndpointPlane.binaryMatrix (1,Equiv.swap (0:Fin 4) 1)=
          !![1,1,1,0;0,1,0,1;0,0,1,1;0,0,0,1] := by decide +kernel
      have hu : ResidualJoinModel.binaryMatrix (.sr 2)=
          !![1,1,0,1;0,1,0,0;0,0,1,1;0,0,0,1] := by decide +kernel
      rw [hb,hu]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply,Fin.sum_univ_succ,unipotentMatrix,shortParameter,CharTwo.add_self_eq_zero]

omit [Finite G] in
private theorem even_plane_mem_residual (a:S4) (ha:a∈alternatingGroup (Fin 4)) :
    sourceEndpointCoreMap c i h.embedding_injective true a∈
      (pResidual 2 (C c i)).map (C c i).subtype := by
  let f : S4→*Dendpoint c i true :=
    (source_Dendpoint_equiv c i h.embedding_injective true).symm.toMonoidHom.comp
      (MonoidHom.inr C2 S4)
  let j : Dendpoint c i true→*C c i:=inclusion ((Dendpoint_le_E c i true).trans inf_le_right)
  have ha' : a∈pResidual 2 S4 := Theory.SpecificGroups.SymmetricFourResidual.residual_eq.symm ▸ ha
  exact ⟨j (f a),map_pResidual_le 2 (j.comp f) (mem_map_of_mem _ ha'),rfl⟩

include h in
theorem source_plane_generator_short_mem_residual (k:Fin 3) :
    sourceEndpointCoreMap c i h.embedding_injective true (Equiv.swap k.castSucc k.succ)*
      sourceMarkedShort c i∈(pResidual 2 (C c i)).map (C c i).subtype := by
  let a:S4:=Equiv.swap k.castSucc k.succ
  let b:S4:=Equiv.swap 0 1
  have hab : a*b⁻¹∈alternatingGroup (Fin 4) := by
    change Equiv.swap k.castSucc k.succ*(Equiv.swap (0:Fin 4) 1)⁻¹∈alternatingGroup (Fin 4)
    rw [Equiv.Perm.mem_alternatingGroup]
    fin_cases k <;> decide +kernel
  have he := even_plane_mem_residual c i z h (a*b⁻¹) hab
  have hb : sourceEndpointCoreMap c i h.embedding_injective true b*sourceMarkedShort c i∈
      (pResidual 2 (C c i)).map (C c i).subtype := by
    rw [plane_swap_short c i h.embedding_injective]
    exact sourceResidualJoin_le_twoResidual c i
      ((sourceResidualJoin_eq_range c i h.embedding_injective).symm ▸ ⟨.sr 2,rfl⟩)
  have hh := ((pResidual 2 (C c i)).map (C c i).subtype).mul_mem he hb
  simpa only [map_mul,map_inv,mul_assoc,inv_mul_cancel_left] using hh

omit [Finite G] in
private theorem native_generator_value (k:Fin 3) :
    (i.comp c.right) ⟨nativeLocalComplementGenerator k,
      nativeLocalComplement_le_plane (subset_closure ⟨k,rfl⟩)⟩=
      sourceEndpointCoreMap c i h.embedding_injective true (Equiv.swap k.castSucc k.succ)*
        sourceMarkedShort c i*Source.graphElement c i := by
  let u:planeParabolicSU F (form F σ hσ):=
    (EndpointPlane.graphFixedPlaneEquivProduct.symm (1,Equiv.swap k.castSucc k.succ)).val
  let a:Extension.plane 1 hn:=Source.planeInclusion
    (((planeParabolicSU F (form F σ hσ)).equivMapOfInjective
      (projection 1 hn) (projection_injective 1 hn)) u)
  let t:Extension.plane 1 hn:=Source.planeInclusion
    (planeParameterMap (Multiplicative.ofAdd (shortParameter F σ)))
  let f:Extension.plane 1 hn:=modelGraph true
  have hg : (⟨nativeLocalComplementGenerator k,
      nativeLocalComplement_le_plane (subset_closure ⟨k,rfl⟩)⟩:Extension.plane 1 hn)=a*t*f := by
    apply Subtype.ext
    rfl
  rw [hg,map_mul,map_mul]
  have ha : (i.comp c.right) a=sourceEndpointCoreMap c i h.embedding_injective true
      (Equiv.swap k.castSucc k.succ) := by
    simp only [sourceEndpointCoreMap,source_Dendpoint_equiv_true,MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom,MonoidHom.inr_apply,Subgroup.coe_subtype]
    rw [source_D_plane_equiv_symm_val]
    rfl
  have ht : (i.comp c.right) t=sourceMarkedShort c i := rfl
  have hf : (i.comp c.right) f=Source.graphElement c i := endpointMap_graph c i true
  rw [ha,ht,hf]

include h in
theorem sourceLocalComplement_le_residual_sup_graph :
    sourceLocalComplement c i≤(pResidual 2 (C c i)).map (C c i).subtype⊔
      zpowers (Source.graphElement c i) := by
  let J:Subgroup G:=(pResidual 2 (C c i)).map (C c i).subtype⊔zpowers (Source.graphElement c i)
  let m:=i.comp c.right
  let L:Subgroup (Extension.ProjectiveExtension 1 hn):=(J.comap m).map (Extension.plane 1 hn).subtype
  have hL : nativeLocalComplement≤L := by
    apply (closure_le _).mpr
    rintro _ ⟨k,rfl⟩
    refine ⟨⟨nativeLocalComplementGenerator k,nativeLocalComplement_le_plane (subset_closure ⟨k,rfl⟩)⟩,?_,rfl⟩
    change m _∈J
    rw [native_generator_value c i z h k]
    exact mul_mem_sup (source_plane_generator_short_mem_residual c i z h k)
      (mem_zpowers (Source.graphElement c i))
  change (nativeLocalComplement.subgroupOf (Extension.plane 1 hn)).map m≤J
  rintro _ ⟨a,ha,rfl⟩
  obtain ⟨b,hb,he⟩:=hL ha
  have hba : b=a := Subtype.ext he
  rw [hba] at hb
  exact hb

include h in
theorem source_Rzero_commutes_localComplement (R:Sylow 2 (C c i)) (hR:Tf c i≤R)
    (r:G) (hr:r∈Rzero c i R) : ∀a∈sourceLocalComplement c i,r*a=a*r := by
  rw [Rzero,source_DtwoResidual_eq_centralizer_residual c i z h R hR] at hr
  have hC : r∈C c i:=Rimage_le_C c i R hr.1
  have hle : (pResidual 2 (C c i)).map (C c i).subtype⊔zpowers (Source.graphElement c i)≤
      centralizer ({r}:Set G) := by
    apply sup_le
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hr.2 x hx)
    · apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hC).symm
  intro a ha
  exact (mem_centralizer_singleton_iff.mp (hle (sourceLocalComplement_le_residual_sup_graph c i z h ha))).symm

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
