module

public import Theory.GroupTheory.ZStar.PrincipalBlockAdapter
public import Theory.GroupTheory.ZStar.CharacterwiseSupport

/-!
# The unconditional principal two-block factory

Every finite group has the exact principal-block package required by the
Z-star induction. The constructed congruence block supplies its ordinary
character data. Principal Brauer equality and the characterwise Nagao trace
give canonical local core support, from which the adapter derives section
invariance and combines it with proved weak block orthogonality.

No modular hypotheses remain in this factory. It is the unconditional final
adapter of `Submission/ZStar/PrincipalBlockFactory.lean` at revision
`c3503435`, using the shared production congruence-block definitions.
-/

public section
namespace Glauberman.ZStar.PrincipalBlockFactory
universe u

/-- The principal two-block package exists uniformly for every finite group. -/
theorem principalTwoBlockData_factory :
    ∀ (G : Type u) [Group G] [Finite G],
      Nonempty (PrincipalTwoBlockData G) := by
  apply principalTwoBlockData_factory_of_canonicalLocalCoreSupport
  intro G _ _ d i hi z hzI
  exact CharacterwiseSupport.canonicalLocalPrincipalBlockCoreSupport d i hi z hzI

end Glauberman.ZStar.PrincipalBlockFactory
