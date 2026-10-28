module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointComparison
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointInvolution

/-!
# The marked ordinary source point endpoint in the literal unitary model

The source residual splitting and the concrete binary-unitary shear supply
two compatible swapped central products. Their factor comparison extends to
the whole point groups. One map carries the source core, central line, module
and Borel to the actual unitary point core, root subgroup, plane module and
flag overlap. No point-model or splitting premise remains.

Source: Aschbacher--Smith 13.5.17, printed p.922, ordinary branch M=L.
Matching this map with the independently recognized plane endpoint is a
separate amalgam compatibility step.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.UnitaryTwo
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
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

/-- The original ordinary point endpoint, with all three source markings,
is the literal point parabolic of U4(2). -/
theorem source_normal_ordinary_point_unitary
    (hordinary : L ⊔ (T : Subgroup G) = L) :
    ∃ v : H, (v : G) ∈ V ∧
      ∃ e : H ≃* pointParabolic 1 (Nat.le_refl 1),
        e v = PointInvolution.involution ∧
        (pCore 2 H).map e.toMonoidHom =
          pCore 2 (pointParabolic 1 (Nat.le_refl 1)) ∧
        (V₁.subgroupOf H).map e.toMonoidHom = PointCore.rootSubgroup ∧
        (V.subgroupOf H).map e.toMonoidHom = PointInvolution.pointModule ∧
        ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf H).map e.toMonoidHom =
          (overlap 1 (Nat.le_refl 1)).subgroupOf (pointParabolic 1 (Nat.le_refl 1)) := by
  obtain ⟨v,hv,e,he,hcore,hline,hmodule,hborel⟩ :=
    normal_ordinary_point_comparison d hA312 hH hU hn hordinary
      PointQuaternion.projectivePointQuaternionData PointResidual.projectivePointResidualData
      PointInvolution.involution PointInvolution.involution_sq
      PointInvolution.involution_complement PointInvolution.involution_swaps_residual.1
  rw [← PointInvolution.pointModule_from_involution] at hmodule hborel
  rw [PointInvolution.pointModule_normalizer] at hborel
  exact ⟨v,hv,e,he,hcore,hline,hmodule,hborel⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source
