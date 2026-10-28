module
public import Theory.Representation.BinaryOffender.IrreducibleSubspaceExistence
public import Theory.GroupTheory.ReducedNormal.MovedWitness
public import Theory.GroupTheory.ReducedNormal.Representation

/-!
# Reduced constituents inside a moved normal module

A.4.11 gives a reduced normal subgroup inside the specified moved module.
The associated invariant subspace of the actual R₂(H) remains noncentral
for a perfect overgroup of the original actor. Its Irr⁺ constituent retains
the original inclusion into the ambient group.

Source: Aschbacher–Smith, A.4.11 and3.2.3, printed pp.60–61 and580.
-/

public section

open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace Theory.GroupTheory.ReducedNormal
variable {G : Type*} [Group G] [Finite G]
theorem exists_irrPlus_subspace_le_of_moved
    (H : Subgroup G) (X Y U : Subgroup H) (hXY : X ≤ Y)
    (hsub : X.IsSubnormal) (hX : IsPPerfect 2 X)
    (hchief : HasCentralPChiefFactorsAbove 2 (pCore 2 X))
    [Group.IsPerfect Y] [U.Normal] [IsElementaryAbelian 2 U]
    (hkill : (pCore 2 X).map X.subtype ≤ centralizer (U : Set H))
    (hmoved : ⁅U,X⁆ ≠ ⊥) :
    ∃ I : Submodule (ZMod 2) (Additive (ModuleGroup H)),
      IsIrrPlus (representation H) Y I ∧ subspaceImage H I ≤ U.map H.subtype := by
  obtain ⟨V,hVU,hV,hVm⟩ :=
    exists_isPReduced_le_of_moved X U hsub hX hchief hkill hmoved
  let := hV.normal
  let J : Submodule (ZMod 2) (Additive (ModuleGroup H)) :=
    AddSubgroup.toZModSubmodule 2 ((V.subgroupOf (ModuleGroup H)).toAddSubgroup)
  have hJ : Y ≤ subspaceStabilizer (representation H) J := by
    apply le_subspaceStabilizer
    intro y hy v hv
    exact (mem_normalizer_iff.mp (V.normalizer_eq_top ▸ mem_top y) v.toMul.val).mp hv
  have hn : ¬ J ≤ fixedSpace (representation H) Y := by
    intro hc
    apply hVm
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro v hv x hx
    have hfix := hc (show Additive.ofMul (⟨v,hV.le_reducedPSubgroup hv⟩ : ModuleGroup H) ∈ J from hv)
      ⟨x,hXY hx⟩
    have he := congrArg (fun w : Additive (ModuleGroup H) => w.toMul.val) hfix
    change x * v * x⁻¹ = v at he
    exact mul_inv_eq_iff_eq_mul.mp he
  obtain ⟨I,hIJ,hI⟩ := exists_isIrrPlus_le_of_not_fixed (representation H) Y J hJ hn
  refine ⟨I,hI,?_⟩
  rintro _ ⟨_,⟨v,hv,rfl⟩,rfl⟩
  exact mem_map_of_mem H.subtype (hVU (hIJ hv))
end Theory.GroupTheory.ReducedNormal
