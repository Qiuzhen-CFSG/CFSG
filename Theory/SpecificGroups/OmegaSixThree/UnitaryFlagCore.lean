module
public import Theory.SpecificGroups.OmegaSixThree.UnitaryFlagComplement
public import Theory.GroupTheory.SylowKernelCore
/-!
# The literal fixed-plane local subgroup and its core

The two marked first-factor involutions generate its Klein four group; the
independent second factor completes the subgroup V4×S4. Its order is96 and
its ambient two-core is exactly the already marked V4×V4 core of H. These
identities identify the image of the native plane graph centralizer and A2.

Source: Aschbacher--Smith F.5.3 and F.5.7, printed pp.300--303.
-/

namespace OmegaSixThree.VertexComparison.FlagWords
open TriangleLocal Subgroup
open Theory.SpecificGroups.SymmetricSix.DuadCalculation (core core_eq)
@[expose] public noncomputable section

def fixedPlaneLocal : Subgroup H := (core.prod ⊤).comap productEquiv.toMonoidHom

def fixedPlaneLocalEquiv : fixedPlaneLocal ≃* core × Four :=
  (((productEquiv.subgroupMap fixedPlaneLocal).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective productEquiv.surjective _))).trans
      (Subgroup.prodEquiv core ⊤)).trans
        (MulEquiv.prodCongr (MulEquiv.refl core) Subgroup.topEquiv)

theorem fixedPlaneLocal_card : Nat.card fixedPlaneLocal=96 := by
  rw [Nat.card_congr fixedPlaneLocalEquiv.toEquiv,Nat.card_prod,
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card,Nat.card_perm,Nat.card_fin]
  decide

theorem fixedPlaneLocal_le_of_marks (K : Subgroup H)
    (hp : pairElement∈K) (hf : graphElement∈K) (hc : complementFactor≤K) :
    fixedPlaneLocal≤K := by
  have hpimg : productEquiv pairElement=(delta,1) := pairElement_image
  intro g hg
  let c : H := productEquiv.symm (1,(productEquiv g).2)
  have hcK : c∈K := hc (by
    change productEquiv c ∈ (⊥ : Subgroup Four).prod ⊤
    rw [productEquiv.apply_symm_apply]
    exact ⟨rfl,mem_top _⟩)
  have hh : (productEquiv g).1=1 ∨ (productEquiv g).1=delta ∨
      (productEquiv g).1=(Equiv.swap 0 3*Equiv.swap 1 2 : Four) ∨
      (productEquiv g).1=delta*(Equiv.swap 0 3*Equiv.swap 1 2 : Four) :=
    (show ∀p:Four,p∈core → p=1 ∨ p=delta ∨ p=(Equiv.swap 0 3*Equiv.swap 1 2) ∨
      p=delta*(Equiv.swap 0 3*Equiv.swap 1 2) by decide +kernel) _ hg.1
  rcases hh with hh|hh|hh|hh
  · have he : g=c := by
      apply productEquiv.injective
      rw [productEquiv.apply_symm_apply]
      exact Prod.ext hh rfl
    exact he ▸ hcK
  · have he : g=pairElement*c := by
      apply productEquiv.injective
      rw [map_mul,hpimg,productEquiv.apply_symm_apply]
      simpa only [Prod.mk_mul_mk,mul_one,one_mul] using (show productEquiv g = ((productEquiv g).1,(productEquiv g).2) from rfl).trans (congrArg (fun p : Four => (p,(productEquiv g).2)) hh)
    exact he ▸ K.mul_mem hp hcK
  · have he : g=graphElement*c := by
      apply productEquiv.injective
      rw [map_mul,graphElement_image,productEquiv.apply_symm_apply]
      simpa only [Prod.mk_mul_mk,mul_one,one_mul] using (show productEquiv g = ((productEquiv g).1,(productEquiv g).2) from rfl).trans (congrArg (fun p : Four => (p,(productEquiv g).2)) hh)
    exact he ▸ K.mul_mem hf hcK
  · have he : g=(pairElement*graphElement)*c := by
      apply productEquiv.injective
      rw [map_mul,map_mul,hpimg,graphElement_image,productEquiv.apply_symm_apply]
      simpa only [Prod.mk_mul_mk,mul_one,one_mul] using (show productEquiv g = ((productEquiv g).1,(productEquiv g).2) from rfl).trans (congrArg (fun p : Four => (p,(productEquiv g).2)) hh)
    exact he ▸ K.mul_mem (K.mul_mem hp hf) hcK

theorem fixedPlaneLocal_core : fixedPlaneLocal.pCoreIn 2 = localCore := by
  apply map_injective (f:=productEquiv.toMonoidHom) productEquiv.injective
  rw [map_pCoreIn_of_injective 2 fixedPlaneLocal productEquiv.toMonoidHom productEquiv.injective]
  have hm : fixedPlaneLocal.map productEquiv.toMonoidHom=core.prod ⊤ :=
    map_comap_eq_self_of_surjective productEquiv.surjective _
  rw [hm,core_map]
  change ((pCore 2 (core.prod (⊤ : Subgroup Four))).map _)=core.prod core
  let e : core.prod (⊤ : Subgroup Four) ≃* core×Four :=
    (Subgroup.prodEquiv core ⊤).trans
      (MulEquiv.prodCongr (MulEquiv.refl core) Subgroup.topEquiv)
  have he := pCore_map_iso 2 e
  have htop : pCore 2 core=⊤ := top_unique (le_sSup
    ⟨inferInstance,(IsElementaryAbelian.isPGroup 2 core).to_subgroup ⊤⟩)
  rw [pCore_prod,htop,←core_eq] at he
  let f : core×Four →* Four×Four := MonoidHom.prodMap core.subtype (MonoidHom.id Four)
  calc
    (pCore 2 (core.prod (⊤ : Subgroup Four))).map _ =
      ((pCore 2 (core.prod (⊤ : Subgroup Four))).map e.toMonoidHom).map f := by
        rw [map_map]; rfl
    _ = ((⊤ : Subgroup core).prod core).map f := by rw [he]
    _ = core.prod core := by
      ext p
      constructor
      · rintro ⟨a,ha,rfl⟩
        exact ⟨a.1.property,ha.2⟩
      · intro hp
        exact ⟨(⟨p.1,hp.1⟩,p.2),⟨mem_top _,hp.2⟩,rfl⟩
end
end OmegaSixThree.VertexComparison.FlagWords
