module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Exterior.Residual
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.RepeatedNatural.Residual

/-!
# The constructed cubic subgroup in the surviving exterior row

The literal row consumer retains K_I/O₂(K_I) ≅ C₃ × SL₃(2), and the
original O^{3′}(O₂,₃(K_I)) has a quotient of order three and three-rank one.
The earlier component identity X=O^{3′}(I) makes this subgroup T-invariant
through the full centralizer C_G(ZS); no T-normality of I or X is assumed.

The component identity remains an earlier-source input with producer
qt-e-152-char2-component-models and final discharge by
qt-e-152-plane-uniqueness. The action and Kc clauses remain with those
owners and qt-e-152-small-parabolic. This consumer constructs the cubic
subgroup, but does not yet exclude it using the action on K/O₂(K).
Original-U recognition and the degree-five minimal-parabolic exclusion
also remain with this terminal-linear family.

Source: Aschbacher--Smith 15.2.23, printed p.1117.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open ChapterB.QuasisimpleSource Section01
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The exterior row constructs the source T-invariant rank-one subgroup,
retaining its actual two-core quotient and the residual model of KI. -/
theorem exterior_cubic_data
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hX : X = (primeToResidual 3 I).map I.subtype)
    {r : ℕ} (hr : r = 2 ∨ r = 3) :
    letI := U_elementary d hI hfit hXI
    Nonempty (ActionEquiv (U_representation d hI hfit hXI hn)
      (SL5TenDimensional.exteriorAction r)) →
    Nonempty ((KI X ZS ⧸ pCore 2 (KI X ZS)) ≃*
        (alternatingGroup (Fin 3) × SL(3,ZMod 2))) ∧
      Nat.card (cubicResidual X ZS ⧸ pCore 2 (cubicResidual X ZS)) = 3 ∧
      primeRank 3 (cubicResidual X ZS) = 1 ∧
      (T : Subgroup G) ≤ normalizer (cubicResidual X ZS : Set G) := by
  let := U_elementary d hI hfit hXI
  intro he
  exact ⟨KI_quotient_of_exterior d hI hfit hXI hn hr he,
    cubicResidual_quotient_card_of_exterior d hI hfit hXI hn hr he,
    cubicResidual_rank_of_exterior d hI hfit hXI hn hr he,
    cubicResidual_normalized d hI hX⟩

/-- The literal row consumer retains the constructed models of both remaining
KI quotients and the original T-invariant cubic subgroup in the exterior case. -/
theorem remaining_rows_with_exterior_cubic
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    letI := U_elementary d hI hfit hXI
    let σ := U_representation d hI hfit hXI hn
    ModuleRow σ →
      (Nonempty ((KI X ZS ⧸ pCore 2 (KI X ZS)) ≃* SL(4,ZMod 2)) ∧
        ∃ r : ℕ, 0 < r ∧ r ≤ 4 ∧
          ∃ e : ActionEquiv σ (repeated (linearNatural BinaryField.two 5) r),
          ∃ v : Fin 5 → ZMod 2, v ≠ 0 ∧
            (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
              e.groupEquiv.toMonoidHom = MulAction.stabilizer SL(5,ZMod 2) v) ∨
      (∃ r : ℕ, (r = 2 ∨ r = 3) ∧ IsIrreducible σ ∧
        Module.finrank (ZMod 2) (Additive (U X ZS)) = 10 ∧
        Nonempty (ActionEquiv σ (SL5TenDimensional.exteriorAction r)) ∧
        Nonempty ((KI X ZS ⧸ pCore 2 (KI X ZS)) ≃*
          (alternatingGroup (Fin 3) × SL(3,ZMod 2))) ∧
        Nat.card (cubicResidual X ZS ⧸ pCore 2 (cubicResidual X ZS)) = 3 ∧
        primeRank 3 (cubicResidual X ZS) = 1 ∧
        (T : Subgroup G) ≤ normalizer (cubicResidual X ZS : Set G)) := by
  let := U_elementary d hI hfit hXI
  dsimp only
  intro hrow
  rcases remaining_rows_with_KI_quotient d hI hfit hXI hn hout hKX hpair hrow with h | h
  · exact Or.inl h
  · obtain ⟨r,hr,hi,hd,he⟩ := h
    exact Or.inr ⟨r,hr,hi,hd,he,exterior_cubic_data d hI hfit hXI hn hX hr he⟩

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
