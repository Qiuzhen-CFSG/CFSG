module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondarySource

/-!
# Secondary source geometry without strict core enlargement

This interface retains the component, torus, core movement and literal
quotient action of original 4.3.11–15. It omits the disputed strict
inequality K₂ < O₂(K_Z)K₂. Proper containment K₂ < K_Z and the proved
bound O₂(K_Z T) ≤ R₂ remain distinct clauses.

The original conditional interface forgets to these data. The construction
from the marked MS inputs is in SourceConstruction; it does not construct
SecondarySourceData. The quotient sieve and terminal representation arguments
must be applied through results proved for this weaker interface.
Source: Aschbacher–Smith, original 4.3.11–15, printed pp.617–618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}

/-- The geometric source interface, with movement of Q only. -/
structure SecondaryActionData (c : SourceConfiguration T L) (n : ℕ) where
  component : Subgroup (rootNormalizer c)
  torus : Subgroup G
  isComponent : component.IsCComponent
  normal : component.Normal
  quasisimple : IsQuasisimple (component ⧸ pCore 2 component)
  secondary_le : secondary c ≤ component.map (rootNormalizer c).subtype
  secondary_lt : secondary c < component.map (rootNormalizer c).subtype
  secondary_model : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ n)
  torus_le : torus ≤ rootNormalizer c
  torus_cyclic : IsCyclic torus
  torus_card : Nat.card torus = 2 ^ n - 1
  torus_faithful : torus ⊓ centralizer (root c : Set G) = ⊥
  torus_secondary : ⁅secondary c,torus⁆ ≤ (secondary c).pCoreIn 2
  torus_normalizes_radical : torus ≤ normalizer (R₂ c : Set G)
  core_eq : (K c ⊔ S c).pCoreIn 2 = Q c
  core_moved : ⁅Q c,torus⁆ = Q c
  radical_le : R₂ c ≤ rootNormalizer c
  radical_normalizer : normalizer (R₂ c : Set G) ≤
    c.H ⊓ normalizer (secondary c : Set G)
  enlarged_core_le : (component.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c
  radical_action : letI := normal
    ((R₂ c).subgroupOf (rootNormalizer c)).map
      (normalQuotientAction component (pCore 2 component)) ≠ ⊥


/-- Literal conjugation on the full quotient K_Z/O₂(K_Z). -/
def SecondaryActionData.action {c : SourceConfiguration T L} {n : ℕ}
    (s : SecondaryActionData c n) :
    rootNormalizer c →* MulAut (s.component ⧸ pCore 2 s.component) := by
  letI := s.normal
  exact normalQuotientAction s.component (pCore 2 s.component)

/-- Retain the genuine source clauses of the original conditional interface. -/
def SecondarySourceData.toActionData {c : SourceConfiguration T L} {n : ℕ}
    (s : SecondarySourceData c n) : SecondaryActionData c n where
  component := s.component
  torus := s.torus
  isComponent := s.isComponent
  normal := s.normal
  quasisimple := s.quasisimple
  secondary_le := s.secondary_le
  secondary_lt := s.secondary_lt
  secondary_model := s.secondary_model
  torus_le := s.torus_le
  torus_cyclic := s.torus_cyclic
  torus_card := s.torus_card
  torus_faithful := s.torus_faithful
  torus_secondary := s.torus_secondary
  torus_normalizes_radical := s.torus_normalizes_radical
  core_eq := s.core_eq
  core_moved := s.core_moved
  radical_le := s.radical_le
  radical_normalizer := s.radical_normalizer
  enlarged_core_le := s.enlarged_core_le
  radical_action := s.radical_action

@[simp] theorem SecondarySourceData.toActionData_action {c : SourceConfiguration T L} {n : ℕ}
    (s : SecondarySourceData c n) : s.toActionData.action = s.action := rfl

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
