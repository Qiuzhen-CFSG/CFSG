module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalInterfaces

/-!
# The final weight-two contradiction from the module decomposition

If the two moved summands in the literal U=⟨Z^Y⟩ are disjoint, invariance
of the L₂-summand under K puts its K-commutators in both summands. They
therefore vanish. The source point in [Z,L₂] has weight two, so its proved
ambient centralizer bound contradicts the escape of K=O²(H).

The decomposition and invariance are explicit inputs to this algebraic
endpoint. The B.5.6 application must prove them, and the source geometry
must construct ProductAnalysis; neither obligation is discharged here.
Source: Aschbacher--Smith, completion of 12.3.1, printed p.812.
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

/-- The actual B.5.6 moved-space conclusions imply the terminal contradiction.
This is a conditional endpoint, not the source elimination theorem. -/
theorem false_of_module_decomposition
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
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
  apply P.residual_escape structural
  exact hK.trans ((centralizer_le (Set.singleton_subset_iff.mpr hv)).trans
    (D.pointCentralizers v hv1 (Or.inl hvw)))

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
