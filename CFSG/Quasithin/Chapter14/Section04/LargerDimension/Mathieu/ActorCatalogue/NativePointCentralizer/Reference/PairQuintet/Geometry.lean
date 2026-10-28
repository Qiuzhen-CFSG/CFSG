module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure

/-!
# Recovering the marked sextet from its remaining pair

A tetrad in a sextet determines its five incident octads: append one point
and use uniqueness of the octad through those five points. Taking differences
recovers the other five tetrads. Thus its stabilizer preserves the sextet.
Conversely, within the stabilizer of {0,9}, the sextet stabilizer preserves
the unique part containing that pair. For the source sextet this part is
{0,2,9,14}, so the remaining pair {2,14} has precisely the quintet stabilizer.

Source: Aschbacher--Smith, H.14 setup and H.14.3, printed pp.396--397
(1 March 2004 manuscript). The octad argument is also used for M23 in
Theory/Mathieu/M23/QuasithinGeometry/SylowTwoLocals/Coverage/TripleLocal.lean.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native

private theorem octad_through_part (S : Sextet) (A : Finset (Fin 24)) (hA : A ∈ S.parts)
    (B : Finset (Fin 24)) (hB : B ∈ m24Blocks) (hAB : A ⊆ B) :
    ∃ D ∈ S.parts, D ≠ A ∧ B = A ∪ D := by
  obtain ⟨x, hx, hxA⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show A.card < B.card by rw [S.tetrad A hA, m24Blocks_card B hB]; decide)
  have hc : x ∈ S.parts.biUnion id := S.cover.symm ▸ Finset.mem_univ x
  obtain ⟨D, hD, hxD⟩ := Finset.mem_biUnion.mp hc
  have hDA : D ≠ A := fun h => hxA (h ▸ hxD)
  have hcard : (insert x A).card = 5 := by
    rw [Finset.card_insert_of_notMem hxA, S.tetrad A hA]
  obtain ⟨C, hC⟩ := Finset.card_eq_one.mp (m24Blocks_unique_block _ hcard)
  have hmem (F : Finset (Fin 24)) (hF : F ∈ m24Blocks) (hAF : insert x A ⊆ F) : F = C := by
    have hm := Finset.mem_filter.mpr ⟨hF, hAF⟩
    change F ∈ m24Blocks.filter (insert x A ⊆ ·) at hm
    simpa only [hC, Finset.mem_singleton] using hm
  refine ⟨D, hD, hDA, (hmem B hB (Finset.insert_subset_iff.mpr ⟨hx, hAB⟩)).trans ?_⟩
  exact (hmem _ (S.octad A hA D hD hDA.symm)
    (Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ hxD, Finset.subset_union_left⟩)).symm

private theorem part_stabilizer_le (S : Sextet) (A : Finset (Fin 24)) (hA : A ∈ S.parts) :
    MulAction.stabilizer M24 A ≤ sextetStabilizer S := by
  intro g hg
  have hgA : g • A = A := hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro D hD
  by_cases he : D = A
  · subst D
    rwa [hgA]
  have hB : g • (A ∪ D) ∈ m24Blocks := by
    have hp := (mem_M24_iff g.val).mp g.property
    change g.val • (A ∪ D) ∈ (m24Blocks : Set (Finset (Fin 24)))
    rw [← hp]
    exact Set.smul_mem_smul_set (S.octad A hA D hD (Ne.symm he))
  obtain ⟨F, hF, hFA, hAF⟩ := octad_through_part S A hA _ hB (by
    rw [Finset.smul_finset_union, hgA]
    exact Finset.subset_union_left)
  have hd := congrArg (fun B : Finset (Fin 24) => B \ A) hAF
  have hl : (g • (A ∪ D)) \ A = g • D := by
    calc
      _ = (g • (A ∪ D)) \ (g • A) := by rw [hgA]
      _ = g • ((A ∪ D) \ A) := Finset.smul_finset_sdiff.symm
      _ = _ := by rw [Finset.union_sdiff_cancel_left (S.disjoint A hA D hD (Ne.symm he))]
  rw [hl, Finset.union_sdiff_cancel_left (S.disjoint A hA F hF hFA.symm)] at hd
  rwa [hd]

/-- The deleted-pair stabilizer preserves the marked sextet exactly when it
preserves its distinguished tetrad. -/
theorem pairQuintet_mem_iff_tetrad (g : MathieuCode.m22PairStabilizer) :
    g ∈ m22OuterQuintetStabilizer m22SourceSextet ↔
      g.val • m22SourceTetrad 0 = m22SourceTetrad 0 := by
  constructor
  · intro hg
    have hm : g.val • m22SourceTetrad 0 ∈ m22SourceSextet.parts :=
      MulAction.mem_stabilizer_finset'.mp hg m22SourceTetrad_mem
    by_contra he
    have hd := m22SourceSextet.disjoint _ hm _ m22SourceTetrad_mem he
    have h0 : g.val • (0 : Fin 24) ∈ g.val • m22SourceTetrad 0 :=
      Finset.smul_mem_smul_finset (by decide +kernel)
    have hpair : g.val • (0 : Fin 24) ∈ m22Pair :=
      MulAction.mem_stabilizer_finset'.mp g.property (by decide +kernel)
    exact Finset.disjoint_left.mp hd h0 (m22Pair_le_sourceTetrad hpair)
  · intro hg
    exact part_stabilizer_le m22SourceSextet _ m22SourceTetrad_mem hg

/-- In the complement of {0,9}, the remaining marked pair is {2,14}. -/
def pairQuintetRemaining : Finset (Fin 24) := {2, 14}

private theorem tetrad_sub_pair : m22SourceTetrad 0 \ m22Pair = pairQuintetRemaining := by
  decide +kernel

private theorem pair_union_remaining : m22Pair ∪ pairQuintetRemaining = m22SourceTetrad 0 := by
  decide +kernel

theorem pairQuintet_mem_iff_remaining (g : MathieuCode.m22PairStabilizer) :
    g ∈ m22OuterQuintetStabilizer m22SourceSextet ↔
      g.val • pairQuintetRemaining = pairQuintetRemaining := by
  rw [pairQuintet_mem_iff_tetrad]
  have hp : g.val • m22Pair = m22Pair := g.property
  constructor
  · intro h
    rw [← tetrad_sub_pair, Finset.smul_finset_sdiff, h, hp]
  · intro h
    rw [← pair_union_remaining, Finset.smul_finset_union, hp, h]

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
