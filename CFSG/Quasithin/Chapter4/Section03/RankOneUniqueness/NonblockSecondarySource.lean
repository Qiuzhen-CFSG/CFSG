module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSetup

/-!
# Source secondary data without universal radical movement

This additive interface retains the geometric, core and literal quotient-action
clauses of the secondary construction. The source gives [Q,Y]=Q; the stronger
Q[R₂,Y]=R₂ is not included. In degree two the original cubic is scalar on the
SL₃(4) quotient, and the diagnostic in `NonblockSecondaryRadical` rules out
that stronger clause for a torus in K.

Legacy data forget to source data, preserving the component and its action.
There is no converse conversion. Source witnesses must additionally retain
Y≤K; it is not inferred merely from normalization. Whole-radical generation
by the secondary group remains a separate mathematical obligation, not a field.
The construction and final nonblock assembly belong to
`qt-d-1222-rankone-uniqueness-nonblock`; the corrected model sieve belongs to
`qt-d-1222-nonblock-endgame-sieve`.

Source: Aschbacher--Smith, original 4.3.11--15, printed pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}

/-- The geometric source interface, with movement of Q only. -/
structure SecondarySourceData (c : SourceConfiguration T L) (n : ℕ) where
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
  core_enlarges : secondary c < (component.map (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c
  radical_action : letI := normal
    ((R₂ c).subgroupOf (rootNormalizer c)).map
      (normalQuotientAction component (pCore 2 component)) ≠ ⊥


/-- Literal conjugation on the full quotient K_Z/O₂(K_Z). -/
def SecondarySourceData.action {c : SourceConfiguration T L} {n : ℕ}
    (s : SecondarySourceData c n) :
    rootNormalizer c →* MulAut (s.component ⧸ pCore 2 s.component) := by
  letI := s.normal
  exact normalQuotientAction s.component (pCore 2 s.component)

/-- Forget the unsupported universal movement clause in the legacy interface. -/
def SecondaryData.toSourceData {c : SourceConfiguration T L} {n : ℕ}
    (s : SecondaryData c n) : SecondarySourceData c n where
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
  core_enlarges := s.core_enlarges
  radical_action := s.radical_action

@[simp] theorem SecondaryData.toSourceData_action {c : SourceConfiguration T L} {n : ℕ}
    (s : SecondaryData c n) : s.toSourceData.action = s.action := rfl

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
