module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.RankTwoCovers
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.ClassicalSimple
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer.RankOne

/-!
# The unitary-two and symplectic-one aliases in source Case II

Both aliases identify the actual central quotient with PSL2 over its original
fixed field. The complete binary PSL2 covering exclusion therefore applies
without a prime-primary-center assumption. These are the low-rank constructors
retained by the full known-simple catalogue.
Source: GLS3 §2.2; Aschbacher--Smith A.2.18, printed p.40.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open HermitianForm.IdentityGram Theory.SpecificGroups.UnitaryRootNormalizer
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G : Type u} [Group G]

/-- Unitary degree two is PSL2 over the actual fixed field, with no simplicity premise. -/
theorem unitary_two_linear_model {a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPSU G 2 (2 ^ a)) : ClassicalGroup.IsPSL G 2 (2 ^ a) := by
  obtain ⟨F, hF, hfin, J, hc, hconj, ⟨e⟩⟩ := iso
  let : CharP F 2 := charP_binary ha hc
  have hk := fixed_card_binary J ha hc hconj
  obtain ⟨ep⟩ := nonempty_projectiveTwoEquiv J hc hk
  exact ⟨FixedBy.subfield F J.conj, inferInstance, inferInstance, hk, ⟨e.trans ep⟩⟩

/-- Symplectic rank one is the literal two-dimensional projective linear group. -/
theorem symplectic_one_linear_model {q : ℕ}
    (iso : ClassicalGroup.IsPSp G 1 q) : ClassicalGroup.IsPSL G 2 q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
  exact ⟨F, hF, hfin, hc,
    ⟨e.trans Theory.SpecificGroups.SymplecticRoot.rankOneProjectiveEquiv⟩⟩

variable [Finite G] [IsQuasisimple G] {K : GroupClass.{u}}
  {S : Type u} [Group S] [Finite S] {p : ℕ}

/-- The complete unitary-two source Case II. -/
theorem caseII_unitary_two_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {a : ℕ} (ha : 2 ≤ a)
    (iso : ClassicalGroup.IsPSU (G ⧸ center G) 2 (2 ^ a)) : False :=
  caseII_linear_two_of_source h ih ha (unitary_two_linear_model (by omega) iso)

/-- The complete symplectic rank-one source Case II. -/
theorem caseII_symplectic_one_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {a : ℕ} (ha : 2 ≤ a)
    (iso : ClassicalGroup.IsPSp (G ⧸ center G) 1 (2 ^ a)) : False :=
  caseII_linear_two_of_source h ih ha (symplectic_one_linear_model iso)

end CFSG.Quasithin.ChapterA.Section02.EvenLie
