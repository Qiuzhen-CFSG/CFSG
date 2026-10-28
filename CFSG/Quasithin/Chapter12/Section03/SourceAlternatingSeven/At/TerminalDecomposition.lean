module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalDecomposition
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalSelection

/-!
# TerminalDecomposition at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalDecomposition`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem false_of_module_decomposition_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : P.ProductAnalysis)
    (hdisjoint : Disjoint ⁅P.U, P.K⁆ ⁅P.U, P.L2⁆)
    (hstable : P.K ≤ normalizer (⁅P.U, P.L2⁆ : Subgroup G))
    (hsecond : ⁅P.U, P.L2⁆ = ⁅P.Z, P.L2⁆) : False := by
  have hL2Y : P.L2 ≤ P.Y := (le_sup_right : P.L2 ≤ P.K ⊔ P.L2).trans le_sup_left
  have hW2U : ⁅P.U, P.L2⁆ ≤ P.U :=
    le_normalizer_iff_commutator_le_left.mp
      (hL2Y.trans (le_normalizer_componentOrbit P.Z P.Y))
  have hcomm : ⁅⁅P.U, P.L2⁆, P.K⁆ = ⊥ := by
    apply le_bot_iff.mp
    apply (le_inf (commutator_mono hW2U le_rfl)
      (le_normalizer_iff_commutator_le_left.mp hstable)).trans
    exact disjoint_iff.mp hdisjoint |>.le
  have hK : P.K ≤ centralizer (⁅P.Z, P.L2⁆ : Subgroup G) := by
    rw [← hsecond]
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  obtain ⟨v, hv1, hvw, hv⟩ := A.weight_two
  apply P.residual_escape_at structural
  exact hK.trans ((centralizer_le (Set.singleton_subset_iff.mpr hv)).trans
    (D.pointCentralizers v hv1 (Or.inl hvw)))

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

