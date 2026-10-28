module

public import Theory.AlgebraicGroup.Borel.ElementCoverage
public import Theory.AlgebraicGroup.Borel.ElementCoverage.RegularWitness.Cartan
public import Theory.AlgebraicGroup.Borel.ElementCoverage.FiniteFiberDensity

/-!
# Every element of a connected algebraic group lies in a Borel conjugate

The actual Cartan component supplies a connected solvable subgroup and a
regular point with finitely many fixed cosets. The proved one-fibre density
theorem makes its conjugacy saturation dense. Completeness of the Borel
homogeneous space makes that saturation closed after passage to a Borel;
Borel conjugacy then gives the prescribed Borel.

Sources: Borel, *Linear Algebraic Groups*, §§11.9(2), 11.10;
GLS3 Theorem 1.6.3. The Ree application supplies torus placement for the
order-five and order-thirteen elements of Guralnick–Malle II, Lemma 8.8.
-/

public section
namespace Theory.AlgebraicGroup.BorelElementCoverage
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- The source element-coverage clause for the original connected group
and an arbitrary specified Borel subgroup. -/
theorem exists_conjugate_mem (hG : Variety.IsConnected G)
    {B : ClosedSubgroup G} (hB : IsBorelSubgroup B) (x : Variety.Point G) :
    ∃ g : Variety.Point G, g⁻¹ * x * g ∈ B.toSubgroup := by
  obtain ⟨H,hH,hsolv,h,hh,hfinite⟩ := exists_connectedSolvable_regularWitness G
  exact exists_conjugate_mem_of_dense_solvable hB H hH hsolv
    (dense_conjugacySaturation_of_finite_fixedPoints hG H hH h hh hfinite) x

end Theory.AlgebraicGroup.BorelElementCoverage
