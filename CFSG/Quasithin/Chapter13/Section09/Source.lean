module
public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.IndependentActions

/-!
# The original wreath exclusion, Theorem 13.9.1

A simple QTKE group has no maximal two-local subgroup containing a Sylow
2-subgroup and isomorphic to S₄ wr C₂. The marking is chosen from the actual
local isomorphism; the source centralizer, fusion, terminal recognition and
independent cubic-action arguments discharge all intermediate premises.

Source: Aschbacher--Smith, Theorem 13.9.1, printed pp.969--974.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09
variable {G : Type*} [Group G] [Finite G] {𝒦 : GroupClass}

/-- Full Theorem 13.9.1, with the original QTKE and wreath configuration. -/
theorem source13_9_1 (hG : IsSimpleQTKE 𝒦 G) (d : Configuration G) : False := by
  obtain ⟨m⟩ := d.exists_marking
  exact m.terminal_cubic_contradiction hG

/-- The literal maximal-local consumer used in 14.1.10 and 15.4.7. -/
theorem false_of_maximal_wreath (hG : IsSimpleQTKE 𝒦 G)
    (T : Sylow 2 G) (M : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M) (e : M ≃* WreathModel) : False :=
  source13_9_1 hG ⟨T, M, hM, hTM, e⟩

end CFSG.Quasithin.Chapter13.Section09
