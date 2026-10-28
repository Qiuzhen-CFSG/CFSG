module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.ReducedSource.LvKernel
public import Theory.GroupTheory.ReducedNormal.Defs

/-!
# Source applicability of the rank-one local action

The larger plus quotient is reduced directly by B.2.13. The actual block
module is generated inside the local seed span, which the local two-core
fixes. The cubic residual quotient and genuine 13.6.11 movement now prove
C_{Lᵥ}(U_K) ≤ C_{Lᵥ}(W_K). Thus `ReducedSource.local_reduced` discharges
the restriction-kernel premise and proves reducedness of the actual KTᵥ
action, from the marked source action and the earlier local and block data.
The literal centralizer-quotient equivalence then gives
`internalWK_isPReduced`, the full B.2.11 certificate in KTᵥ.

The Baumann image-containment assembly and its E.2.3 input remain in
SourceImage. Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.11–18, printed pp.928–931.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.ReducedSource

variable {G : Type*} [Group G] [Finite G]

/-- Source B.2.11 for the actual internal W_K in KTᵥ. Its quotient is
KTᵥ/C_{KTᵥ}(W_K), identified with the range of the restricted plus map. -/
theorem internalWK_isPReduced {L V : Subgroup G} (m : Marking L V) (K T : Subgroup G)
    (hk : m.action.ker = pCore 2 L)
    (hL : Tv T (markedV m) ≤ normalizer (Lv L (markedV m) : Set G))
    (hz : Tv T (markedV m) ≤ centralizer ({markedZ m} : Set G))
    (hK : K ∈ Yz L T (markedZ m) (markedV m))
    (hnorm : Tv T (markedV m) ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T (markedZ m) (markedV m))]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : Matrix.SpecialLinearGroup.RankOneResidual.NaturalSection (F := F)
      (componentRepresentation K L T (markedZ m) (markedV m) hL hz)
      (movingSpace K L T (markedZ m) (markedV m)))
    (hzOmega : markedZ m ∈ omegaOneCenterAmbient (Tv T (markedV m)))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T (markedV m)) (Gv (markedV m)))
    (hf : Theory.GroupTheory.generalizedFitting (Gv (markedV m)) = pCore 2 (Gv (markedV m))) :
    Theory.GroupTheory.IsPReduced 2
      (internalWK K L T (markedZ m) (markedV m) hL hz) := by
  refine ⟨internalWK_normal K L T _ _ hL hz,
    internalWK_elementary K L T _ _ hL hz, ?_⟩
  have hW := (WK_le_Tv K L T _ _ hK.1.1 hSylow hzOmega hf).trans
    (show Tv T (markedV m) ≤ K ⊔ Tv T (markedV m) from le_sup_right)
  let e := localCentralizerQuotientEquiv K L T (markedZ m) (markedV m) hL hz hW
  rw [← pCore_map_iso 2 e.symm,
    local_reduced m K T hk hL hz hK hnorm hF hb s hzOmega hSylow hf, Subgroup.map_bot]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.ReducedSource
end
