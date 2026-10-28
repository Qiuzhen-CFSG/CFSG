module

public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SourceTheorems

/-!
# Thompson factors when the actual reduced action is solvable

B.2.7 supplies the stable family of nontrivial images of the original
maximum elementary subgroups. Its generated subgroup is exactly the
image of J(G), with the given centralizer quotient map retained.
Apply the proved solvable FF theorem B.1.8 to that actual quotient action.
The original group need not be solvable: only its action image is.

The result constructs the concrete internal SL₂(2) factors and their
equivariant natural binary supports, and identifies the image of J(G)
with the nonempty product selected by the original stable family.
No factor witness or identification of J(G) with all offenders is assumed.
This is the reduced-action use of solvable Thompson factorization in
Aschbacher–Smith 14.1.4 and 14.1.7, printed pp.976–977; its inputs are
B.2.7 and B.1.8, printed pp.70 and 76.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Construct the actual Thompson-image factors from solvability of its faithful action. -/
theorem thompson_factors_of_solvable_action
    {H : Type*} [Group H] [Finite H]
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (T : Sylow 2 G) (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hsolv : Group.IsSolvable H) (hcore : pCore 2 H = ⊥) :
    let ρ := NormalElementaryQuotient.representation U q hq hker
    let P := ChapterB.maxOffenderImages (⊤ : Subgroup G) U q
    ∃ d : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      Representation.BinaryOffender.IsStable (V := Additive U) ρ P ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q = generatedBy P ⊤ ∧
      (d.toSolvableFFFactors.stableFactorSet P).Nonempty ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q =
        ⨆ i ∈ d.toSolvableFFFactors.stableFactorSet P, d.factor i := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  let P := ChapterB.maxOffenderImages (⊤ : Subgroup G) U q
  obtain hf | ⟨_, hff, hstable, hgen, _⟩ := ChapterB.lemma_B_2_7 U q hq hker T
  · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
  obtain ⟨d⟩ := ChapterB.solvableFFStructure_nonempty ρ hsolv hcore
    (NormalElementaryQuotient.representation_injective U q hq hker) hff
  have hfaith := NormalElementaryQuotient.representation_injective U q hq hker
  exact ⟨d, hstable, hgen,
    d.toSolvableFFFactors.stableFactorSet_nonempty hfaith d.ratio_one hstable,
    hgen.trans (d.toSolvableFFFactors.stable_generatedBy_eq hfaith d.ratio_one hstable)⟩


end CFSG.Quasithin.ChapterB
