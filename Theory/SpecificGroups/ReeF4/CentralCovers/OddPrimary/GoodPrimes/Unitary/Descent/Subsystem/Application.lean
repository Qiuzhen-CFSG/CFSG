module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Singer

/-!
# Full unitary and Singer tori in the actual Ree groups

The constructed split subsystem discharges the geometric premise of the
existing faithful unitary descent. Its diagonal cubic kernel meets the
unitary graph trivially; Lang conjugacy and the original coefficient map
place the full SU₃ in the literal finite Ree model. Restricting this embedding
to the checked norm-one and Singer actions gives both torus orders required
by the good-prime central-cover calculation, retaining the scalar three-part.
All statements hold for the source range m ≥ 1 and have no torus premise.
Source: GLS3 Example 2.6.3, Table 4.7.3A and §4.10.
-/

public section
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent

/-- The source's split subsystem exists over the original coefficient closure. -/
theorem nonempty_subsystem (m : ℕ) :
    Nonempty (SubsystemData m (AlgebraicClosure (CoefficientField m))) :=
  Subsystem.nonempty_data _ m

/-- Full SU₃ embeds faithfully into the original finite Ree carrier. -/
theorem exists_unitary_embedding (m : ℕ) (hm : 1 ≤ m) :
    ∃ j : (Three.form m).specialSubgroup →* Model m, Function.Injective j :=
  exists_embedding_of_subsystem m hm (Subsystem.data _ m)

/-- Both full unitary torus witnesses required by the actual good-prime assembly. -/
theorem nonempty_tori (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) + 1)) ∧
      Nonempty (CyclicTorusEmbedding m ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1)) := by
  obtain ⟨j, hj⟩ := exists_unitary_embedding m hm
  exact nonempty_tori_of_special_embedding j hj

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent
