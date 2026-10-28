module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors.Geometry

/-!
# The positioned outer four-group branch

The actual residual supplement of the inner involution centralizer is now a
rank-one E-member for the original outer actor. Failure of escape traps the
whole centralizer and the source's solvable and odd local generators.

The proved matrix generation theorem forces any subgroup containing these
controls to be the whole graph extension. Thus some genuine rank-one E-member
for the original family escapes every proper overgroup of its weak-closure
normalizer. This discharges the order-four premise of
`familyEscapes_of_positioned_outer_cases`, without an additional local-structure,
generation or strongly-quasithin premise.

Source: Aschbacher--Smith E.1.1--5 and E.1.14(7), printed pp.209--210, 214;
A.3.21(a), p.55; Aschbacher, GF(2)-representations of finite groups (1982),
Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- Conditional assembly from an explicit matrix-generation input.
It retains the literal family and produces an actual escaping rank-one E-member. -/
theorem familyEscapes_of_positioned_four_actor_of_generation {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (hgeometry : FourActorCentralizerGeneration F)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω) (hlarge : LargeActors F T Ω)
    (houter : ¬ HasInnerActor F T Ω) (M : Subgroup (graphExtension F))
    (hTM : (T : Subgroup _) ≤ M) (hproper : M ≠ ⊤)
    (hNM : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M)
    (A : Subgroup (graphExtension F)) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _))
    (hfour : Nat.card A = 4) (hinner : Nat.card (A ⊓ innerPart F : Subgroup _) = 2)
    (z : graphExtension F) (hz : orderOf z = 2) (hzL : z ∈ innerPart F) (hzA : z ∈ A)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _)) : FamilyEscapes F T Ω M := by
  classical
  by_contra hnot
  obtain ⟨hCM, hsol, hodd⟩ := positioned_four_controls_of_no_escape F hp ho hl hF
    hΩ hlarge hA hAT hfour hinner hz hzL hzA hTz hTM hproper hNM hnot
  exact hproper (hgeometry T Ω hΩ hlarge houter A hA hAT hfour hinner z hz hzL hzA hTz
    M hCM hNM hsol hodd)

/-- The positioned outer four-group branch of E.1.14(7). All local E-member
clauses and matrix-generation inputs are discharged. The escaping member uses
an actor from the original family; strong quasithinness is not needed. -/
theorem familyEscapes_of_positioned_four_actor {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω) (hlarge : LargeActors F T Ω)
    (houter : ¬ HasInnerActor F T Ω) (M : Subgroup (graphExtension F))
    (hTM : (T : Subgroup _) ≤ M) (hproper : M ≠ ⊤)
    (hNM : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M)
    (A : Subgroup (graphExtension F)) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _))
    (hfour : Nat.card A = 4) (hinner : Nat.card (A ⊓ innerPart F : Subgroup _) = 2)
    (z : graphExtension F) (hz : orderOf z = 2) (hzL : z ∈ innerPart F) (hzA : z ∈ A)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _)) : FamilyEscapes F T Ω M := by
  exact familyEscapes_of_positioned_four_actor_of_generation F hp ho hl hF
    (fourActorCentralizerGeneration F hp ho hl hF) T Ω hΩ hlarge houter M hTM hproper hNM
    A hA hAT hfour hinner z hz hzL hzA hTz

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
