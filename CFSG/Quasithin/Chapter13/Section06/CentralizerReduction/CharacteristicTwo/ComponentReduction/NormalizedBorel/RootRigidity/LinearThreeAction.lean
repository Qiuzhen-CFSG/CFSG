module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ActionFacts
public import Theory.SpecificGroups.PSL3.NormalizedRootCentralizers.ResidualAction

/-!
# The marked residual has inner-diagonal PSL₃ action

Central descent through the actual component action transports the source
identity Lᵥ = [Lᵥ,Tᵥ] to the quotient of Aut(PSL₃) by its inner-diagonal
subgroup. That quotient is abelian, so the field part vanishes. This retains
the central cover and the actual maps; no splitting of an outer extension
is used. `ResidualAction.residual_commutator` in the parent supplies the
explicit commutator premise from the A₅ marking.

Source: Aschbacher–Smith, A.3.16–18 and proof of 13.6.6, printed p.927.
-/

public section
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
variable {G : Type*} [Group G] {L V : Subgroup G}

/-- The literal quotient's residual action is inner-diagonal, including
when the original component is an exceptional central cover of PSL₃(4). -/
theorem residualStar_linearThree_innerDiagonal
    (s : Marking L V) (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    {F : Type*} [Field F] [Finite F]
    (e : K ⧸ center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (hcover : Matrix.PSL3.OuterSolvable.standard F = ⊤)
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K)
    (hcomm : ⁅residual s, localT T (markedV s)⁆ = residual s) :
    (residualStar s K).map
      ((MulAut.centralQuotientAction e).comp (NormalizerAction.action K)) ≤
        Matrix.PSL3.OuterSolvable.innerDiagonal F := by
  let D := (residual s).subgroupOf (X K)
  let P := (localT T (markedV s)).subgroupOf (X K)
  have hDP : ⁅D, P⁆ = D := by
    apply map_injective (X K).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hDN, map_subgroupOf_eq_of_le hTN, hcomm]
  change (D.map (NormalizerAction.quotient K)).map _ ≤ _
  rw [map_map]
  exact Matrix.PSL3.NormalizedRootCentralizers.commutator_generated_innerDiagonal
    _ D P hDP hcover

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
