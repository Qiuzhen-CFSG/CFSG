module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalContainment
public import Theory.SpecificGroups.BinaryComponentResidual

/-!
# Local containment on each concrete surviving binary component

The actual model equivalences supply all center, three-rank and outer-group
facts. The original residual L₁ lies in K and the original K is normal in H.
No universal A.3.18 input or normality callback remains in these model cases.
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

/-- Actual A₆ equivalence discharges all ordinary residual-model facts. -/
theorem source_local_containment_six (K : Subgroup G)
    (s : let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩; Selected D K)
    (e : Source.starImage H K ≃* alternatingGroup (Fin 6)) :
    residualCentralizer L V₁ ≤ K ∧ (K.subgroupOf H).Normal := by
  have f := Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv e
    Theory.SpecificGroups.BinaryComponentResidual.alternatingSix
  exact source_local_containment d hA312 hH hU K s f.1 f.2.1 f.2.2

/-- Actual binary SL₄ or SL₅ equivalence discharges all ordinary residual-model facts. -/
theorem source_local_containment_linear (K : Subgroup G)
    (s : let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩; Selected D K)
    {n : ℕ} (hn : n=4 ∨ n=5)
    (e : Source.starImage H K ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    residualCentralizer L V₁ ≤ K ∧ (K.subgroupOf H).Normal := by
  have f := Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv e
    (Theory.SpecificGroups.BinaryComponentResidual.linear hn)
  exact source_local_containment d hA312 hH hU K s f.1 f.2.1 f.2.2

/-- The genuine G₂(2)′ model discharges all ordinary residual-model facts. -/
theorem source_local_containment_g2 (K : Subgroup G)
    (s : let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩; Selected D K)
    (e : Source.starImage H K ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    residualCentralizer L V₁ ≤ K ∧ (K.subgroupOf H).Normal := by
  have f := Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv e
    Theory.SpecificGroups.BinaryComponentResidual.g2
  exact source_local_containment d hA312 hH hU K s f.1 f.2.1 f.2.2
end CFSG.Quasithin.Chapter13.Section05.A5Source
