module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.OddLocals
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.CentralizerRoute
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.PrimeCentralizer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.Unmarked

/-!
# Local constructions for positioned outer eight-group actors

The odd-local construction retains the original actor, establishes the intrinsic
Sylow intersection in the join with ambient tau, and extracts an actual
rank-one E-member from an escaping odd commutator. It also permits the inner
four-group as a subactor of that commutator, without adding it to the family.
The centralizer route assembles two explicit model inputs: generation for the
restricted family inside the centralizer, and subsequent matrix generation.

For p > 5, the literal radical quotient of the centralizer supplement has
PSL₂(F) simple socle. The two existing prime-field linear geometries and
the odd-torus mixing construction suffice; split mixing is discharged.
At five, families containing a four-actor are already settled. The remaining
finite geometry has two alternatives: a solvable Sylow overgroup generating
with the weak-closure normalizer, or an original actor with outer four-group
image in the literal S₅ quotient. The latter consumes the independent
positioned S₅ theorem. Every remaining input below must still be supplied
before asserting the unconditional `familyEscapes_of_positioned_eight_actor`.

Source: Aschbacher--Smith E.1.1--5, E.1.8, E.1.10 and E.1.14(7),
pp.209--214; Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory GorensteinWalter
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
open EightActors PSLTwoGeneration.PrimeGeometry
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

local instance : Finite (PGL2 F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- Assembly of the exact positioned-eight branch. The existing prime-field
and odd-torus producers, the finite prime-five geometry and the positioned
S₅ theorem remain explicit; this does not claim the unconditional source result. -/
theorem familyEscapes_of_positioned_eight_actor_of_remaining_inputs {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (hinner : 5 < p → ∀ S : Sylow 2 (PSL2 F), ConcreteLocalGeometryAt S)
    (hdiagonal : 5 < p → ∀ S : Sylow 2 (PGL2 F), ConcreteLocalGeometryAt S)
    (hnonsplit : p % 4 = 3 → InnerGenerationGeometry.FourGroupOddMixing F)
    (hgeometry : p = 5 → FiveEightGeometry F)
    (hfive : ∀ (S : Sylow 2 (Equiv.Perm (Fin 5))) (B : Subgroup (Equiv.Perm (Fin 5))),
      IsElementaryAbelian 2 B → Nat.card B = 4 → B ≤ (S : Subgroup _) →
      ¬ B ≤ alternatingGroup (Fin 5) → eSubgroup 1 (S : Subgroup _) B ⊔ (S : Subgroup _) = ⊤)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω) (hlarge : LargeActors F T Ω)
    (houter : ¬ HasInnerActor F T Ω) (M : Subgroup (graphExtension F))
    (hTM : (T : Subgroup _) ≤ M) (hM : M ≠ ⊤)
    (hN : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M)
    (A : Subgroup (graphExtension F)) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _))
    (hcard : Nat.card A = 8) (hfour : Nat.card (A ⊓ innerPart F : Subgroup _) = 4)
    (z : graphExtension F) (hz : orderOf z = 2) (hzL : z ∈ innerPart F) (hzA : z ∈ A)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _)) : FamilyEscapes F T Ω M := by
  classical
  by_cases h5 : p = 5
  · have hc5 : Nat.card F = 5 := hF.trans h5
    by_cases hsmall : ∃ B ∈ Ω, B ≤ (T : Subgroup _) ∧ Nat.card B = 4
    · obtain ⟨B, hB, hBT, hc⟩ := hsmall
      exact familyEscapes_of_four_actor_at_five F hc5 T Ω hΩ hlarge houter
        M hTM hM hN B hB hBT hc
    · have honly : ∀ B ∈ Ω, B ≤ (T : Subgroup _) → B ≠ ⊥ → Nat.card B = 8 := by
        intro B hB hBT hne
        let _ := hΩ.1 B hB
        exact (large_actor_card F hp ho hF B (hlarge B hB hBT hne)).resolve_left
          (fun hc => hsmall ⟨B, hB, hBT, hc⟩)
      exact familyEscapes_of_five_geometry F hc5 hfive T Ω hΩ hlarge M hTM hM hN
        z hz hzL hTz (hgeometry h5 T Ω hΩ hlarge houter honly
          A hA hAT hcard hfour z hz hzL hzA hTz)
  · have hp5 : 5 < p := by
      have := Nat.odd_iff.mp ho
      omega
    exact familyEscapes_of_positioned_eight_actor_of_prime_geometry F hp ho hp5 hF
      (hinner hp5) (hdiagonal hp5) hnonsplit
      T Ω hΩ hlarge houter M hTM hM hN A hA hAT hcard hfour z hz hzL hzA hTz

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
