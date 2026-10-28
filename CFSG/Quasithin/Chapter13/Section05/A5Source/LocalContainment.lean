module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.FittingAction
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ResidualStructure
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.SourceLocalContainment

/-!
# Original A₅ local containment in the surviving component

The original context supplies the cubic local quotient and SQTK rank bound.
Only the actual selected component's three model facts remain: trivial
center, three-rank at least two, and two-group outer automorphisms. The
ordinary A.3.18 argument proves L₁≤K and normality in the original H.
Source: Aschbacher–Smith13.5.21(1), p.924.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ComponentReduction Recognition
open Representation Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
include d hA312 hH hU

/-- The actual original L₁ lies in K in the ordinary centerless binary-model cases. -/
theorem source_local_containment (K : Subgroup G)
    (s : let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩; Selected D K)
    (hz : center (Source.starImage H K) = ⊥)
    (hr : 2 ≤ primeRank 3 (Source.starImage H K))
    (ho : IsPGroup 2 (MulAut.Outer (Source.starImage H K))) :
    residualCentralizer L V₁ ≤ K ∧ (K.subgroupOf H).Normal := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  exact s.local_le_of_binary_component hf (residual_quotient_card d hA312 hH hU)
    hz hr ((source_local_sqtk d hH).stronglyQuasithin 3 (by decide) (by decide)) ho
end CFSG.Quasithin.Chapter13.Section05.A5Source
