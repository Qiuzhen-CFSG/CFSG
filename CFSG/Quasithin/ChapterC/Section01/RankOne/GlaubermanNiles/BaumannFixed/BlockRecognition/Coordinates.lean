module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.BlockRecognition.Actor
public import Theory.SpecificGroups.SL2.Affine.Action
/-!
# Literal coordinates on the residual block layer

The original quotient map restricts onto F*(H*), with kernel O₂(O²H).
The checked equality U(O²H)=V=moved transports the actual fixed denominator
and conjugation. First-isomorphism maps therefore give a BlockModuleModel
for the derived natural rank-one action, retaining its original actor
identification even over F₂.

Source: Aschbacher–Smith C.1.17–18, printed p.126; Campbell II.8, p.38.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles.BlockRecognition
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}
variable (h : InLocalClass e) (hB : IsBaumannFixed B)
    (hc : ⁅pResidual 2 H,pCore 2 H⁆≤Campbell.V H)

include h hB in
theorem residual_image : (pResidual 2 H).map (QuotientGroup.mk' (localKernel e))=
    generalizedFitting (LocalStar e) := by
  rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _),localStar_fitting_eq_residual h hB]

def residualActor : pResidual 2 H →* generalizedFitting (LocalStar e) :=
  ((QuotientGroup.mk' (localKernel e)).comp (pResidual 2 H).subtype).codRestrict _
    (fun x => (residual_image h hB).le (mem_map_of_mem _ x.property))

theorem residualActor_surjective : Function.Surjective (residualActor h hB) := by
  intro x
  obtain ⟨l,hl,he⟩ := (residual_image h hB).ge x.property
  exact ⟨⟨l,hl⟩,Subtype.ext he⟩

include hc in
theorem residualActor_ker : (residualActor h hB).ker=pCore 2 (pResidual 2 H) := by
  rw [pCore_subnormal_eq_comap 2 (inferInstance : (pResidual 2 H).Normal).isSubnormal]
  ext l
  change (⟨QuotientGroup.mk' (localKernel e) (l:H),_⟩:generalizedFitting (LocalStar e))=1 ↔ (l:H)∈pCore 2 H
  rw [Subtype.ext_iff]
  change QuotientGroup.mk' (localKernel e) (l:H)=1 ↔ _
  change (QuotientGroup.mk (l:H):H⧸localKernel e)=1 ↔ _
  rw [QuotientGroup.eq_one_iff, kernel_eq_core_of_residual_commutator_le h hB hc]

def residualCoreEquiv : (pResidual 2 H⧸pCore 2 (pResidual 2 H))≃*
    generalizedFitting (LocalStar e) :=
  (QuotientGroup.quotientMulEquivOfEq (residualActor_ker h hB hc).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (residualActor_surjective h hB))

variable {F : Type} [Field F] [Finite F] [CharP F 2] (m : NaturalModel e F)

def residualUEquiv : blockU (pResidual 2 H)≃*moved e :=
  ((blockU (pResidual 2 H)).equivMapOfInjective (pResidual 2 H).subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr ((residual_blockU_map_eq_campbellV h hB hc).trans
      (h.campbellV_eq_moved hB m)))

theorem residualUEquiv_coe (u : blockU (pResidual 2 H)) :
    (residualUEquiv h hB hc m u:H)=u := rfl

theorem residualUEquiv_fixed :
    (blockFixed (pResidual 2 H)).map (residualUEquiv h hB hc m).toMonoidHom=movedFixed e := by
  rw [movedFixed_eq_residual_centralizer_of_bound h hB hc]
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    intro l hl
    exact congrArg Subtype.val (mem_center_iff.mp hu ⟨l,hl⟩)
  · intro hx
    obtain ⟨u,rfl⟩ := (residualUEquiv h hB hc m).surjective x
    refine ⟨u,?_,rfl⟩
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext (hx (l:H) l.property)

def residualModuleEquiv : BlockModule (pResidual 2 H)≃*MovedModule e :=
  QuotientGroup.congr _ _ (residualUEquiv h hB hc m) (residualUEquiv_fixed h hB hc m)

theorem residualModuleEquiv_mk (u : blockU (pResidual 2 H)) :
    residualModuleEquiv h hB hc m (QuotientGroup.mk' (blockFixed (pResidual 2 H)) u)=
      QuotientGroup.mk' (movedFixed e) (residualUEquiv h hB hc m u) := rfl

def derivedNaturalAction (F : Type) [Field F] [CharP F 2] :
    commutator PSL(2,F)→*MulAut (Multiplicative (Fin 2→F)) :=
  (Matrix.SL2.naturalAction F).comp
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm.toMonoidHom.comp
      (commutator PSL(2,F)).subtype)

def residualNaturalModel : BlockModuleModel (pResidual 2 H) (derivedNaturalAction F) where
  quotientIso := (residualCoreEquiv h hB hc).trans m.actorIso
  moduleIso := (residualModuleEquiv h hB hc m).trans m.moduleIso
  intertwining l u := by
    let a:actorLift e:=⟨l,by
      rw [actorLift_eq_residual_sup_core_of_bound h hB hc]
      exact (show pResidual 2 H≤pResidual 2 H⊔pCore 2 H from le_sup_left) l.property⟩
    have he := m.intertwining a (residualUEquiv h hB hc m u)
    apply Multiplicative.toAdd.injective
    exact he
end CFSG.Quasithin.ChapterC.GlaubermanNiles.BlockRecognition
