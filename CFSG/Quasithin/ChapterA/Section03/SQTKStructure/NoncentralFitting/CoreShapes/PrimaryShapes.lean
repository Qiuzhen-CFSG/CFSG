module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.PrimaryShapes.Extraspecial
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.PrimaryShapes.Inversion
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.PrimaryShapes.Homocyclicity

/-!
# Primary-core shapes in the noncentral Fitting branch

Every prime in F(L) has a constructed rank-two supercritical seed with the
actual Frattini-action kernel F(L). The extraspecial branch is complete,
including saturation of the whole core, order p³ and exponent p.

In the elementary branch, involution inversion makes the whole core abelian,
and the actual perfect action then gives homocyclic coordinates. Both steps
are discharged in `primary_shapes`, preserving every positive homocyclic
exponent. The conditional assembly interface is retained separately.

The output is exactly the `hshape` argument of
`CoreShapes.structure_of_prime_core_data`; the parent retains the other
source branches and final A.3.6 assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6,
printed pp.44–45.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.RankActions
open CFSG.Quasithin.Chapter1.Section02 LocalModels
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes
universe u
variable {G : Type u} [Group G] [Finite G] {L : Subgroup G}

/-- Conditional assembly of the two full-core branches. The seed construction
and the entire extraspecial branch are discharged here; `primary_shapes` below
also discharges the two elementary implications. -/
theorem primary_shapes_of_elementary_steps
    (hrigid : PrimeSL2CoverRigidity.{u})
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hquot : PrimeSL2FittingQuotient L)
    (habelian : ∀ (p : ℕ) [Fact p.Prime] (s : PrimarySeed p L),
      Nat.card s.X = p ^ 2 →
      Nonempty (s.X ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))) →
      IsMulCommutative (pCore p L))
    (hhomocyclic : ∀ (p : ℕ) [Fact p.Prime] (_s : PrimarySeed p L),
      IsMulCommutative (pCore p L) → HomocyclicTwo p (pCore p L)) :
    ∀ (p : ℕ) [Fact p.Prime], p ∣ Nat.card (fittingSubgroup L) →
      OddExtraspecialThree p (pCore p L) ∨ HomocyclicTwo p (pCore p L) := by
  intro p _ hd
  obtain ⟨s⟩ := exists_primarySeed hrigid hG hO hL hquot hd
  rcases s.models with ⟨hc, he⟩ | he
  · exact Or.inr (hhomocyclic p s (habelian p s hc he))
  · exact Or.inl (extraspecial_core hrigid hL hquot s he)

/-- Every primary core in F(L) is extraspecial of order p³ and exponent p,
or homocyclic of rank two with a positive exponent. This supplies the exact
`hshape` premise of `CoreShapes.structure_of_prime_core_data`, using only the
given prime-field Fitting quotient and cover rigidity. -/
theorem primary_shapes
    (hrigid : PrimeSL2CoverRigidity.{u})
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hquot : PrimeSL2FittingQuotient L) :
    ∀ (p : ℕ) [Fact p.Prime], p ∣ Nat.card (fittingSubgroup L) →
      OddExtraspecialThree p (pCore p L) ∨ HomocyclicTwo p (pCore p L) := by
  let : Group.IsPerfect L := hL.perfect
  exact primary_shapes_of_elementary_steps hrigid hG hO hL hquot
    (fun _ _ s hc he => elementary_core_abelian hG hO hL hquot s hc he)
    (fun _ _ s hab => homocyclic_core s hab)

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes
