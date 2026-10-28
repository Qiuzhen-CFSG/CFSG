module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceOrthogonalWitness
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CubicNormalizer

/-!
# The original orthogonal cubic normalizer bounds H*

The actual cubic/singular witness is fed to the finite plus-space normalizer
classification. It identifies the original image normalizer with S₃×S₃ and
its cubic centralizer with C₃×S₃. The unchanged injective starred action
therefore bounds |H*| by divisibility into36. Equality remains a later
source obligation; no H* recognition conclusion is assumed.

Source: Aschbacher–Smith13.5.15, printed p.920.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceStarBound
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceOrthogonal SourceOrthogonalWitness
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
  (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

theorem original_normalizer_models :
    Nonempty ((normalizer (localCubic d h e hseed hn hU:Set BinaryFourPlus.Wreath))≃*
      Equiv.Perm (Fin 3)×Equiv.Perm (Fin 3)) ∧
    Nonempty ((centralizer (localCubic d h e hseed hn hU:Set BinaryFourPlus.Wreath))≃*
      Multiplicative (ZMod 3)×Equiv.Perm (Fin 3)) := by
  obtain ⟨_,hA,_,s,_,hs,_,hss,hc⟩ := exists_original_cubic_normalizer_witness d h e hseed hn hU
  exact BinaryFourPlus.CubicNormalizer.normalizer_centralizer_models _ hA s hs hss hc

theorem original_normalizer_card :
    Nat.card (normalizer (localCubic d h e hseed hn hU:Set BinaryFourPlus.Wreath))=36 ∧
    Nat.card (centralizer (localCubic d h e hseed hn hU:Set BinaryFourPlus.Wreath))=18 := by
  obtain ⟨_,hA,_,s,_,hs,_,hss,hc⟩ := exists_original_cubic_normalizer_witness d h e hseed hn hU
  exact BinaryFourPlus.CubicNormalizer.normalizer_centralizer_card _ hA s hs hss hc

theorem original_star_card_dvd : Nat.card (Section08.Source.Hstar D.H)∣36 := by
  let f := starEmbedding d h e hseed hn hU
  let A := localCubic d h e hseed hn hU
  have hr : f.range≤normalizer (A:Set BinaryFourPlus.Wreath) := range_normalizes_local d h e hseed hn hU
  let j : Section08.Source.Hstar D.H→*normalizer (A:Set BinaryFourPlus.Wreath) :=
    f.codRestrict _ (fun x=>hr ⟨x,rfl⟩)
  have hj : Function.Injective j := fun x y he=>(starEmbedding_injective d h e hseed hn hU)
    (congrArg (fun z => (z.val : BinaryFourPlus.Wreath)) he)
  exact (card_dvd_of_injective j hj).trans ((original_normalizer_card d h e hseed hn hU).1 ▸ dvd_rfl)

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceStarBound
end
