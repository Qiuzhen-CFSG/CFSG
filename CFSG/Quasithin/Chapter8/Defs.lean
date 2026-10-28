module

public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic

/-!
# The centralizer span in the Fischer-shadow argument

For an actual weak-closure offender `A = N_{Vᵍ}(V)`, §8.1 uses the
subgroups `C_A(V) ≤ B ≤ A` of corank five in `Vᵍ`, and the subgroup generated
by their centralizers in `V`. These are ambient subgroups, with their actual
conjugation actions; no group-family labels or numerical certificates enter
the definitions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), proof of Theorem 8.1.3, printed pp. 713–714.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter8
open Subgroup ChapterE
variable {G : Type*} [Group G]

/-- The family denoted by `B` in the last two paragraphs of 8.1.3, with a
variable corank to expose the centralizer-rigidity argument. -/
def offenderCorankFamily (V : Subgroup G) (g : G) (k : ℕ) : Set (Subgroup G) :=
  {B | B ≤ offenderNormalizer V g ∧
    offenderNormalizer V g ⊓ centralizer (V : Set G) ≤ B ∧
    subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B = k}

/-- The literal span `⟨C_V(B) : B ∈ B⟩` from 8.1.3. -/
noncomputable def offenderCentralizerSpan (V : Subgroup G) (g : G) (k : ℕ) :
    Subgroup G :=
  ⨆ (B : Subgroup G) (_ : B ∈ offenderCorankFamily V g k),
    V ⊓ centralizer (B : Set G)

end CFSG.Quasithin.Chapter8
