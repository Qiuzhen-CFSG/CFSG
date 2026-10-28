module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour.Contracts
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour.QuotientBlocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour.Geometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour.LayerBlocks
public import CFSG.Quasithin.Chapter1.Section01

/-!
# The J4 local block cover

For the actual ATLAS E2048.M24 subgroup of `Janko4.Model`, the two-core is
nontrivial and self-centralizing and every subnormal chi-zero block is
excluded. Thus this subgroup has the required even-local and block properties
whenever it contains the supplied subgroup S.

For the prescribed `LocalSetup`, `Geometry` pulls back a Sylow-adapted
Mathieu subgroup through the actual quotient map and adjoins the supplied S.
It proves containment in L ∨ S, nontrivial self-centralizing two-core,
generation with C_G(z), and an actual Mathieu two-layer series. `LayerBlocks`
excludes every relatively subnormal chi-zero block in this local overgroup.
Together these construct `CentralizerBlockCover` with no extra premises,
retaining the central two-kernel and allowing S to permute components.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526; GLS3, Table 5.3i.
The parent sporadic exclusion assembly can apply
`LocalSetup.false_of_centralizerBlockCover` to the resulting cover.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour

open Subgroup Janko4.Cardinality Janko4.LocalStructure

variable (hA : Janko4.matrixA * Janko4.matrixA = 1)
  (hB : Janko4.matrixB ^ 4 = 1)

/-- The concrete local subgroup is even-local over every subgroup it contains.
The inclusion premise still has to be established for the actual supplied Sylow. -/
theorem max1_mem_HeOver (S : Subgroup Janko4.Model) (hS : S ≤ max1Subgroup hA hB) :
    max1Subgroup hA hB ∈ Chapter1.HeOver Janko4.Model (S : Set Janko4.Model) := by
  refine ⟨Chapter1.mem_He_iff.mpr ?_, ?_, hS⟩
  · rw [← localKernel_eq_twoCore hA hB, centralizer_localKernel]
  · change (pCore 2 (max1Subgroup hA hB)).map (max1Subgroup hA hB).subtype ≠ ⊥
    intro he
    have hb := ((pCore 2 (max1Subgroup hA hB)).map_eq_bot_iff_of_injective
      Subtype.val_injective).mp he
    exact localKernel_ne_bot hA hB ((localKernel_eq_twoCore hA hB).trans hb)

/-- The actual local subgroup excludes every relative subnormal chi-zero block. -/
theorem max1_blockObstruction (M S : Subgroup Janko4.Model) :
    BlockObstruction M S (max1Subgroup hA hB) := by
  intro B hb _
  exact (max1_no_chiZero_subnormal hA hB B hb.1.subnormal hb.2).elim

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The J₄ calculation in 2.3.9(7): the actual quotient and action supply
a generating local block cover for the prescribed Sylow subgroup. -/
theorem nonempty_centralizerBlockCover (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) :
    Nonempty (CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) := by
  obtain ⟨c⟩ := exists_mathieuLocalCover h d
  exact ⟨c.toCentralizerBlockCover M⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour

end
