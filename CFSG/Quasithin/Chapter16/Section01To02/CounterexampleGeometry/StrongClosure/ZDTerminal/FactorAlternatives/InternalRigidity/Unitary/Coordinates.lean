module

public import Theory.SpecificGroups.SU3.StronglyClosedPairs.Coordinates

/-!
# Torus fusion of commuting Hermitian root factors

The reusable coordinate proof, including the stronger elementary-factor clause,
lives in `Theory.SpecificGroups.SU3.StronglyClosedPairs.Coordinates`.
This wrapper preserves the chapter interface used in the terminal argument of
Aschbacher (1975), Lemma 3.4, p.96.
-/

open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.InternalRigidity.UnitaryCoordinates
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- Torus-invariant unions of commuting Hermitian root factors are nested. -/
public theorem factors_nested [Finite E] [CharP E 2] {q : ℕ}
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = q^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) (hq : 2 < q)
    (B C : Subgroup (hermitianUnipotentCoord J))
    (hcomm : ∀ z ∈ B, ∀ w ∈ C, Commute z w)
    (hclosed : ∀ (k : Eˣ) z, z ∈ B ∨ z ∈ C →
      hermitianTorusAction J k z ∈ B ∨ hermitianTorusAction J k z ∈ C) :
    B ≤ C ∨ C ≤ B := by
  exact (HermitianForm.StronglyClosedPairs.Coordinates.factors_nested_elementary
    J hJ hcard hfixed hq B C hcomm hclosed).imp And.left And.left

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.InternalRigidity.UnitaryCoordinates
