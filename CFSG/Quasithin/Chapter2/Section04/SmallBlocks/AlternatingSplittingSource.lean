module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingBorelSource
public import Theory.Representation.BinaryAlternatingFiveExtension.Splitting
/-!
# Splitting the original alternating-five block

The marked action on the literal kernel is obtained by restricting the
original symmetric-five quotient to L. Its Borel is the inverse image of
an actual point stabilizer. The regular Sylow restriction of the binary
natural module then gives a complement, using the proved regular-kernel
splitting theorem and Gaschütz.

This supplies the original extension marks for the Borel residual and
extraspecial subgroup in Aschbacher–Smith 2.4.29, printed pp.544–545.
-/

public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_kernel_borel_model
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    ∃ (q : d.block →* alternatingGroup (Fin 5))
      (e : q.ker ≃* Multiplicative (core (Fin 5))) (i : Fin 5),
      Function.Surjective q ∧ q.ker = blockU d.block ∧
      (M.subgroupOf d.H).subgroupOf d.block =
        (MulAction.stabilizer (alternatingGroup (Fin 5)) i).comap q ∧
      ∀ (g : d.block) (v : q.ker), e (MulAut.conjNormal g v) =
        Multiplicative.ofAdd (coreRepresentation (Fin 5) (q g).val (e v).toAdd) := by
  obtain ⟨q,e,i,hq,hk,hB,he⟩ := d.single_alternating_block_borel_model hG T hST hsingle hA
  let E := MulEquiv.subgroupCongr hk
  let e' := E.trans e
  refine ⟨q,e',i,hq,hk,hB,?_⟩
  intro g v
  apply e'.symm.injective
  rw [e'.symm_apply_apply]
  apply Subtype.ext
  exact (he g (E v)).symm

theorem MinimalBlockSetup.single_alternating_block_splits
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    ∃ C : Subgroup d.block, (blockU d.block).IsComplement' C := by
  obtain ⟨q,e,i,hq,hk,_,he⟩ := d.single_alternating_kernel_borel_model hG T hST hsingle hA
  rw [←hk]
  exact BinaryPermutation.AlternatingFiveExtension.exists_complement q hq e he
end CFSG.Quasithin.Chapter2
