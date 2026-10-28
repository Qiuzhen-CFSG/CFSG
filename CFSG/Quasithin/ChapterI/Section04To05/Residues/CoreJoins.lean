module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PairQuotients
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores

/-!
# The irreducible local-core joins in I.5.7

The line quotient has parabolic two-cores of order two. The PSL₃(2) and
A₆ quotients have parabolic two-cores of order four, irreducible under the
parabolic. Applying the literal pair-quotient maps therefore proves the
source core-join identity for the line-plane pair and for the A₆ point-line
branch. The S₆ point branch is deliberately left to its separate D5 argument.

Source: Aschbacher–Smith I.5.7(1), printed p.420.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] {D : Diagram} (S : DSystem D G)

theorem line_standard_quotientMark :
    ∃ e : (S.family 1 ⧸ pCore 2 (S.family 1)) ≃* SymmetricThreeProduct.G,
      ((localParabolic S.family 1 0).map (S.localQuotientMap 1 e) =
          SymmetricThreeProduct.leftParabolic ∧
        (localParabolic S.family 1 2).map (S.localQuotientMap 1 e) =
          SymmetricThreeProduct.rightParabolic) ∨
      ((localParabolic S.family 1 0).map (S.localQuotientMap 1 e) =
          SymmetricThreeProduct.rightParabolic ∧
        (localParabolic S.family 1 2).map (S.localQuotientMap 1 e) =
          SymmetricThreeProduct.leftParabolic) := by
  obtain ⟨e⟩ := S.line_quotient
  apply S.exists_standard_quotientMark 1 0 2 S.line_parabolics e
  intro T
  obtain ⟨g, _, h⟩ := SymmetricThreeProduct.coatom_over_sylow T
  exact ⟨g, h⟩

private theorem digon_core_card (U : Subgroup SymmetricThreeProduct.G)
    (h : U = SymmetricThreeProduct.leftParabolic ∨ U = SymmetricThreeProduct.rightParabolic) :
    Nat.card (pCore 2 U) = 2 := by
  rcases h with rfl | rfl
  · rw [SymmetricThreeProduct.left_twoCore]
    exact SymmetricThreeProduct.card_ker_leftQuotientMap
  · rw [SymmetricThreeProduct.right_twoCore]
    exact SymmetricThreeProduct.card_ker_rightQuotientMap

private theorem linear_core_data (U : Subgroup Matrix.PSL3Two.PSL)
    (h : U = Matrix.PSL3Two.pointParabolic ∨ U = Matrix.PSL3Two.lineParabolic) :
    Nat.card (pCore 2 U) = 4 ∧
      ∀ N : Subgroup U, N.Normal → N ≤ pCore 2 U → N = ⊥ ∨ N = pCore 2 U := by
  rcases h with rfl | rfl
  · refine ⟨Matrix.PSL3Two.pointParabolic_core_data.2, ?_⟩
    intro N hn hN
    let := hn
    exact Matrix.PSL3Two.pointParabolic_normal_le_core N hN
  · refine ⟨Matrix.PSL3Two.lineParabolic_core_data.2, ?_⟩
    intro N hn hN
    let := hn
    exact Matrix.PSL3Two.lineParabolic_normal_le_core N hN

/-- The line-plane equality of I.5.7(1), from the original D-system alone. -/
theorem line_plane_core_join : (S.pair 1 2).pCoreIn 2 = S.Q 1 ⊔ S.Q 2 := by
  obtain ⟨e, he⟩ := S.plane_standard_quotientMark
  obtain ⟨d, hd⟩ := S.line_standard_quotientMark
  have hlin := linear_core_data _ (he.symm.imp And.right And.right)
  have htwo := digon_core_card _ (hd.symm.imp And.right And.right)
  have h := S.pair_core_join_of_local_models 2 1 e d hlin.1 htwo hlin.2
  simpa only [pair, inf_comm, sup_comm] using h

variable (S₃ : DSystem .C3 G)

private theorem alternating_core_data (U : Subgroup Theory.SpecificGroups.SymmetricSix.A6)
    (h : U = Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer ∨
      U = Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer) :
    Nat.card (pCore 2 U) = 4 ∧
      ∀ N : Subgroup U, N.Normal → N ≤ pCore 2 U → N = ⊥ ∨ N = pCore 2 U := by
  rcases h with rfl | rfl
  · refine ⟨Theory.SpecificGroups.SymmetricSix.a6DuadCore_card, ?_⟩
    intro N hn hN
    let := hn
    exact Theory.SpecificGroups.SymmetricSix.a6DuadCore_irreducible N hN
  · refine ⟨Theory.SpecificGroups.SymmetricSix.a6SynthemeCore_card, ?_⟩
    intro N hn hN
    let := hn
    exact Theory.SpecificGroups.SymmetricSix.a6SynthemeCore_irreducible N hN

/-- The A₆ point branch of I.5.7(1), with the actual source quotient. -/
theorem point_line_core_join_of_alternating
    (e₀ : (S₃.family 0 ⧸ pCore 2 (S₃.family 0)) ≃*
      Theory.SpecificGroups.SymmetricSix.A6) :
    (S₃.pair 0 1).pCoreIn 2 = S₃.Q 0 ⊔ S₃.Q 1 := by
  obtain ⟨e, he⟩ := S₃.exists_standard_quotientMark 0 1 2 S₃.point_parabolics e₀
    Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer
    Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer (fun T => by
      obtain ⟨g, _, h⟩ := Theory.SpecificGroups.SymmetricSix.a6_coatoms_over_sylow T
      exact ⟨g, h⟩)
  obtain ⟨d, hd⟩ := S₃.line_standard_quotientMark
  have ha := alternating_core_data _ (he.imp And.left And.left)
  have htwo := digon_core_card _ (hd.imp And.left And.left)
  exact S₃.pair_core_join_of_local_models 0 1 e d ha.1 htwo ha.2

end Quasithin.I5.DSystem
