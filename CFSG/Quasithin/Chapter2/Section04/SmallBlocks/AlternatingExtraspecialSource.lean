module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSplittingSource
public import Theory.Representation.BinaryAlternatingFiveExtension.Borel
/-!
# The original alternating-five Borel core

The literal action on the selected block identifies its intersection with M
with an A4 Borel preimage. The natural-module extension calculation then
makes the two-core of its two-residual a central product of two quaternion
groups. Both exports retain the actual ambient subgroup and its two-core.

Source: Aschbacher–Smith 2.4.29, printed p.540.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_borel_residual_quaternion
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    Nonempty (QuaternionCentralProductData
      (pCore 2 (pResidual 2 (M ⊓ d.block.map d.H.subtype : Subgroup G)))) := by
  obtain ⟨q,e,i,hq,_,hB,he⟩ := d.single_alternating_kernel_borel_model hG T hST hsingle hA
  obtain ⟨hp⟩ := BinaryPermutation.AlternatingFiveExtension.borel_residual_quaternion q hq e he i
  rw [←hB] at hp
  let B := (M.subgroupOf d.H).subgroupOf d.block
  let A := M ⊓ d.block.map d.H.subtype
  let f : B →* A :=
    { toFun := fun b => ⟨b,⟨b.property,mem_map_of_mem d.H.subtype b.val.property⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : A => (z : G)) h
    · intro a
      obtain ⟨l,hl,hla⟩ := a.property.2
      refine ⟨⟨⟨l,hl⟩,?_⟩,Subtype.ext hla⟩
      change (l : G) ∈ M
      have hh : (l : G) = (a : G) := hla
      exact hh.symm ▸ a.property.1
  let eb := MulEquiv.ofBijective f hf
  let er := (eb.subgroupMap (pResidual 2 B)).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 eb.toMonoidHom eb.surjective))
  let ep := (er.subgroupMap (pCore 2 (pResidual 2 B))).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 er))
  exact ⟨hp.map ep⟩

theorem MinimalBlockSetup.single_alternating_borel_core_quaternion
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    Nonempty (QuaternionCentralProductData (K.pCoreIn 2)) := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  obtain ⟨hp⟩ := d.single_alternating_borel_residual_quaternion hG T hST hsingle hA
  let er := (pResidual 2 B).equivMapOfInjective B.subtype B.subtype_injective
  let ep := (er.subgroupMap (pCore 2 (pResidual 2 B))).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 er))
  let ea := (pCore 2 K).equivMapOfInjective K.subtype K.subtype_injective
  exact ⟨hp.map (ep.trans ea)⟩
end CFSG.Quasithin.Chapter2
