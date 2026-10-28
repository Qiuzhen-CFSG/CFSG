module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.ThompsonImage.SourceAction.Construction.Faithfulness
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.ThompsonImage.SourceAction.Construction.Offenders

/-!
# Construction of the full covered-six source action

The marked commutator places the irreducible block in W_K. Conjugation then
descends to G⁺; its kernel is a normal two-group and is trivial by the earlier
R₂ consequence. The exact hexacode normalizer constructs the full embedding
extending the prescribed component coordinates. The actual nontrivial images
of maximum elementary subgroups of Tᵥ are best offenders on this same block.

The explicit earlier inputs are the genuine A₅ marking and central seed
(p.926), the two-group consequence of Uᵥ∈R₂(Gᵥ) (p.928), membership in Y_z
and O₂(G⁺)=1 from W_K∈R₂ (p.929), Tᵥ-invariance from 13.6.14, and Lᵥ≤K from
13.6.20. The parent source assembly retains their provenance and discharge.
The component comparison supplies f and its equation on representatives;
neither injectivity of f nor a two-group plus kernel is additionally needed.
The hexacode model m is the independently constructed model of the given
exceptional block. There are no additional B.4/B.5/C.1 implications to discharge.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.926–932, especially the paragraph before 13.6.14 and 13.6.22.
The Thompson four-group and subsequent normalizer geometry remain with the
parent assembly.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage.Construction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction ComponentSelection A5Module
variable {G : Type*} [Group G] [Finite G] {K L V T : Subgroup G}

/-- Construct the full source model and all its actual maximum-elementary offender images from the earlier source inputs. -/
theorem exists_source_plusBlockModel
    (s : A5Module.Marking L V) (h : IsExceptionalAhat6Block K)
    [IsElementaryAbelian 2 (blockU K)] (m : HexacodeModel h)
    (hK : K ∈ Yz L T (markedZ s) (markedV s))
    (hn : Tv T (markedV s) ≤ normalizer (K : Set G))
    (hL : Tv T (markedV s) ≤ normalizer (Lv L (markedV s) : Set G))
    (hz : Tv T (markedV s) ≤ centralizer ({markedZ s} : Set G))
    (hzT : markedZ s ∈ Tv T (markedV s))
    (hU : IsPGroup 2 (Uv (markedZ s) (markedV s)))
    (hLK : Lv L (markedV s) ≤ K)
    (f : (K ⧸ pCore 2 K) →* Gplus K L T (markedZ s) (markedV s) hL hz)
    (hf : ∀ k : K, f (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T (markedZ s) (markedV s) hL hz (inclusion (K_le_plusActor K L T (markedV s)) k))
    (hcore : pCore 2 (Gplus K L T (markedZ s) (markedV s) hL hz) = ⊥) :
    ∃ d : PlusBlockModel K L T (markedZ s) (markedV s) h hL hz m f,
      ∀ A ∈ elementaryAbelianMaxSubgroups (Tv T (markedV s)),
        plusImage K L T (markedZ s) (markedV s) hL hz A ≠ ⊥ →
          IsBestOffender d.action (plusImage K L T (markedZ s) (markedV s) hL hz A) := by
  have hUW := blockU_le_WK s h m hK hn hL hz hzT hU hLK
  obtain ⟨d⟩ := nonempty_plusBlockModel_of_block_le hL hz h m f hf hn hLK hUW hK hcore
  exact ⟨d, fun A hA hne => plusBlockModel_maxElementary_isBestOffender d hK hn hLK A hA hne⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage.Construction
