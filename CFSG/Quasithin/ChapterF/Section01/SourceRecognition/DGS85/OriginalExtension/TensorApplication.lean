module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Applications
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.SizeBound

/-!
# Original tensor-Sylow bound after reduced DGS structure

Apply the full-Borel extension calculation to the literal pair consisting
of O²(H) and the selected cubic factor U. Its common Borel is the original
BT. A reduced bound on O₂(BT) therefore controls the original ambient
Sylow T, without replacing T by a Sylow of a smaller completion.

The only new premise is the reduced structural order bound supplied by
the DGS Chapter 10/11 branches. This is the local original-versus-reduced
step in Aschbacher–Smith 9.3.1, printed pp.732–733, and F.1.12, pp.262–264.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Chapter3.Section02 MixedZeroCore
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The actual BT core bound yields the bound on the original T used by 9.3.1. -/
theorem mixed_cubic_factor_size_of_reduced_borel_bound
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥)
    (hred : Nat.card (pCore 2 (B ⊔ (T : Subgroup G) : Subgroup G)) ≤ 128) :
    Nat.card T ≤ 256 := by
  obtain ⟨hf, _, _, _, hb, _, _⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  obtain ⟨eU⟩ := hU.2.2.2.2
  apply ChapterF.Source.DGS85.OriginalExtension.mixed_original_sylow_le_256_of_reduced_order
    hf eK eU
  change Nat.card (ChapterF.Source.twoCore (ChapterF.Source.commonBorel
    ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G))) ≤ 128
  rw [hb]
  exact (card_map_of_injective (B ⊔ (T : Subgroup G) : Subgroup G).subtype_injective).le.trans hred

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
