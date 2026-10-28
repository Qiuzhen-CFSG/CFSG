module
public import CFSG.Quasithin.ChapterG.Section05.Structure.PairSmallSubmodules
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryFixedKernel
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations.MarkedModules

/-!
# The marked cubic bound on small pair submodules

The specified duad cubic is the outer image of the common syntheme
cubic. Restrict the fixed-kernel map from the G.5.3 flag to that exact
actor. Its target is the contragredient augmentation cover, whose fixed
index is four. Hence every pair submodule of dimension at most five has
at most one noncentral binary cubic constituent for this marking.

Source: Aschbacher--Smith 13.8.33, printed p.968. The literal source
quotient application is OriginalCentralizerCubic; no natural-or-cover
identification of the whole centralizer quotient is assumed here.
-/

public section
open Representation BinaryPermutation
open Representation.BinaryFixedPoints
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open A6Endgame.ActionAnalysis33.ChiefModels

private noncomputable def cubicAlternating : cubicActor →* alternatingGroup (Fin 6) :=
  (Marked.outer.toMonoidHom.comp cubicActor.subtype).codRestrict _ (by
    intro a
    obtain ⟨n,hn⟩ := cubicGenerator_generates a
    rw [← hn,map_zpow]
    apply Subgroup.zpow_mem
    change Marked.outer Marked.pairCycle ∈ alternatingGroup (Fin 6)
    rw [outer_pairCycle]
    decide)

/-- Every at-most-five-dimensional pair submodule has at most one moved
binary cubic constituent under the original duad marking. -/
theorem small_pair_cubic_fixedIndex_le
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) X)
    (j : ρ.IntertwiningMap SixPairsQuadratic.action) (hj : Function.Injective j)
    (hd : Module.finrank (ZMod 2) X ≤ 5) :
    fixedIndex (ρ.comp (Marked.outer.toMonoidHom.comp cubicActor.subtype)) ≤ 4 := by
  let _ : Finite (Module.Dual (ZMod 2) Augmentation) :=
    Finite.of_injective (fun f => (f : Augmentation → ZMod 2)) DFunLike.coe_injective
  obtain ⟨f,hfix⟩ := ChapterG.Section05.Structure.small_pair_dual_cover_map ρ j hj hd
  have hb := fixedIndex_le_of_fixed_kernel
    (ρ.comp (Marked.outer.toMonoidHom.comp cubicActor.subtype)) oppositeAugmentationDual
    cubicGenerator cubicGenerator_generates cubicGenerator_cube f.toLinearMap
    (fun a x => IntertwiningMap.isIntertwining _ _ f (cubicAlternating a) x)
    (fun x hx => hfix x hx (Marked.outer cubicGenerator.val))
  exact hb.trans_eq oppositeAugmentationDual_fixedIndex

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
