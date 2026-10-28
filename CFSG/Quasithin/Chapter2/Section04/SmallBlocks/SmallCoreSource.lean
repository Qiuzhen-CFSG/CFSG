module
public import CFSG.Quasithin.Chapter2.Section04.CoreSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.SourceRecognition
public import CFSG.Quasithin.ChapterC.Section06.CubicSmallCore

/-!
# The literal small-core A₃ shadow

For the original single selected A₃ block, Q=U makes the ambient Sylow group
dihedral or semidihedral by C.6.1's self-centralizing-four argument. The proved
full I.4.3 recognition and the original unique-local exclusions then give
the exact Theorem 2.4.1 model list. No Sylow classification is a premise.

Source: Aschbacher--Smith 2.4.26, printed p.543, using C.6.1(6b).
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_cubic_small_core_sylow
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hK : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3)
    (hsmall : twoCore d.H = d.U0.map d.H.subtype) :
    IsDihedralGroup T ∨ IsSemidihedralGroup T := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hi
  have hMR : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM).mp hn
  have hlt : R < M₀ := lt_of_le_of_ne hSM (by
    intro he
    have hh : R.relIndex M₀ = 1 := relIndex_eq_one.mpr he.ge
    change R.relIndex M₀ = 2 at hi
    omega)
  obtain ⟨c⟩ := d.original_hypotheses T hST.le M₀ hlt hMT hMR
  rw [hsingle] at c
  have hRK := c.R_le_H.trans c.normalizes_residual
  apply ChapterC.Section06.cubic_small_core_sylow c hK T T.isPGroup' hST
    (fun W hW hWS hHW => lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST.le
      W hW hWS ((normal_subgroupOf_iff_le_normalizer
        (hWS.trans (map_subtype_le _))).mpr hHW))
  exact hsmall.trans (d.single_block_closures hRK).2

theorem MinimalBlockSetup.single_cubic_small_core_classification
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hK : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3)
    (hsmall : twoCore d.H = d.U0.map d.H.subtype)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty) : IsTheorem241Model G :=
  SmallBlocks.source_small_sylow_recognition_complete hG T M hM hu hdelta
    (d.single_cubic_small_core_sylow T hST hsingle hK hsmall)

end CFSG.Quasithin.Chapter2
