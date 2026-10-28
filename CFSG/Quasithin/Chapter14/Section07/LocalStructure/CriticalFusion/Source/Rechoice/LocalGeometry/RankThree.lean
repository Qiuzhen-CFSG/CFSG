module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Sections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Elementary

/-!
# Initial rank-three conclusions for the original critical pair

This application establishes the elementary geometry, actual centralizer
and normalization by the two vertex cores and their two-residual. All
subgroups use the same source path. The only extra earlier input is the
central commutator bound of 14.5.15(1), with producer qt-14-05; the
preparation producer supplies `Preliminary`.

The full rank-three family is not yet assembled here. The restricted
F.9.7 pairing must supply the full two-axis action, relative normality and
residual generation. The original-cover normalizer calculation and the
three-axis contradiction must establish T-normalization. Finally the
actual 14.7.65 fixed-space and L₁ actions must identify the orbit-span.
Their final assembly remains qt-14-07-rechoice-rank-three-action.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
proof of 14.7.70, printed p.1074 (PDF p.1091).
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
open Subgroup Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- Initial source conclusions, derived from the genuine prepared pair and
the earlier central-commutator bound, with no local action conclusion assumed. -/
theorem initial_geometry (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (h : Preliminary d c) (h15 : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1) :
    IsElementaryAbelian 2 (E c) ∧ primeRank 2 (E c) = 2 ∧
      IsPGroup 2 (centralizer (E c : Set G)) ∧
      YE c ≤ normalizer (E c : Set G) ∧
      Y c ≤ normalizer (E c : Set G) ∧
      conjugateSpanBy (F.Vi 1) (Y c) ≤ E c ∧
      primeRank 2 (↥(V ⊔ c.Zα)) = 4 :=
  ⟨h.E_elementary, h.E_rank, h.E_centralizer_two, h.YE_normalizes h15,
    h.Y_normalizes h15, h.residual_span_le h15, h.seed_sup_opposite_rank⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
