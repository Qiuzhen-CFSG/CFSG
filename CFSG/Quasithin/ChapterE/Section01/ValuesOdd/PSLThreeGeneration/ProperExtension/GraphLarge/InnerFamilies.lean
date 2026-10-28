module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Centralizer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry

/-!
# Large inner families in odd-prime PSL₃ graph extensions

Every large inner actor is a four-group containing a common Sylow-central
involution. Its image modulo the radical of the involution-centralizer
residual supplement has rank at most one. The checked reduction recovers the
full centralizer from this supplement. The component calculation and the
matrix generation theorem now discharge both local inputs: failure of family
escape traps the centralizer, solvable full-Sylow overgroups and the controlled
odd commutators, which together generate the entire graph extension.

Thus every large family containing an inner actor has an actual escaping
rank-one E-member. The final consumer below leaves only the separate
outer-family construction explicit; it does not assert the full graph case.

Source: Aschbacher--Smith, E.1.2, E.1.5 and E.1.14(7), printed pp.210, 214;
Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.11.
-/

public section
open Subgroup
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge

variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- The large-inner-family branch of E.1.14(7). Both model inputs are proved
for the literal graph extension. The original elementary family, intrinsic
radical quotient and local tau are retained throughout the construction. -/
theorem familyEscapes_of_hasInnerActor {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hbig : 3 < p) (hF : Nat.card F = p)
    (_hstrong : IsStronglyQuasithin (graphExtension F))
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω) (hlarge : LargeActors F T Ω) (hi : HasInnerActor F T Ω)
    (M : Subgroup (graphExtension F)) (hTM : (T : Subgroup (graphExtension F)) ≤ M)
    (hproper : M ≠ ⊤)
    (hNM : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M) :
    FamilyEscapes F T Ω M :=
  familyEscapes_of_inner_centralizer_and_generation F hp ho hF
    (innerCentralizerStructure F hp ho hbig hF)
    (innerCentralizerGeneration F hp ho hbig hF)
    T Ω hΩ hlarge hi M hTM hproper hNM

/-- Application to the graph-model generation reduction. The inner-family
premise is discharged; only the independent outer-family branch remains. -/
theorem isEGenerated_one_of_outer_families {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hbig : 3 < p) (hF : Nat.card F = p)
    (hstrong : IsStronglyQuasithin (graphExtension F))
    (houter : ∀ (T : Sylow 2 (graphExtension F)) Ω,
      IsElementaryFamily Ω → LargeActors F T Ω → ¬ HasInnerActor F T Ω →
      ∀ M : Subgroup (graphExtension F), (T : Subgroup (graphExtension F)) ≤ M →
        M ≠ ⊤ → normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M →
          FamilyEscapes F T Ω M) : IsEGenerated 1 (graphExtension F) :=
  isEGenerated_one_of_inner_and_outer_families F
    (familyEscapes_of_hasInnerActor F hp ho hbig hF hstrong) houter

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
