module
public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.SourceSylow
public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.ModelFixers

/-!
# Model consequences for the original terminal residual

Apply the proved A4 pointwise-fixer theorems to the original first and second
S4 factors and H=O²(C_G(E)). The PSL3(2) recognition branch forces all of M₁
to centralize H. The A6 branch contradicts the original quasithin rank bound.
Only recognition of this same H remains an input; no local action or fixer
hypothesis is assumed here.
Source: Aschbacher--Smith, proof of 13.9.1, printed p.974.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath TerminalSubgroup
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} (m : Marking d)

omit [Finite G] in
/-- The recognized PSL3(2) is centralized by the original first factor. -/
theorem terminal_centralized_of_psl3Two
    (eH : terminal m.terminalFour ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    m.factor 1≤centralizer (terminal m.terminalFour:Set G) :=
  centralizes_of_psl3Two _ _ _ m.terminalFour_eq_factorCore
    m.first_factor_centralizes_second_residual m.second_residual_le_terminal
    (m.factorResidualEquiv turn) eH

/-- Quasithin excludes the A6 recognition branch for the actual H. -/
theorem false_of_terminal_alternatingSix (hG : IsQuasithin G)
    (eH : terminal m.terminalFour ≃* alternatingGroup (Fin 6)) : False :=
  false_of_alternating_six hG _ _ _ m.terminalFour_eq_factorCore
    m.first_factor_centralizes_second_residual m.second_residual_le_terminal
    (m.factorResidualEquiv 1) (m.factorResidualEquiv turn) eH

end CFSG.Quasithin.Chapter13.Section09.Marking
