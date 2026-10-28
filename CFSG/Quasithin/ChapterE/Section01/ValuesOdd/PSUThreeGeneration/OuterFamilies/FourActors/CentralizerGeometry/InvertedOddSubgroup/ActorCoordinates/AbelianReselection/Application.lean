module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection

/-!
# Applying cyclic-core reselection to the actual coordinate consumer

The cyclic-core dichotomy and exceptional fusion imply the literal `hselect`
used by `exists_positioned_inverted_coordinates_of_abelian_reselection`.
This leaf imports both the provider and the consumer, without a reverse import.
The final application discharges both local inputs using the actual unitary
model. Only the independent intrinsic coordinate geometry remains explicit;
its discharge belongs to the coordinate-assembly owner.

Source: Aschbacher--Smith E.1.14(7), printed p.214, and its cited
Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
open AbelianReselection
variable {G : Type*} [Group G] [Finite G]

/-- Discharge the reselection premise of the existing coordinate consumer
from the two explicit cyclic-core inputs. Their source producers are separate. -/
theorem exists_positioned_inverted_coordinates_of_cyclicCoreData
    [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hfour : Nat.card A = 4)
    (hout : ¬ A ≤ generalizedFitting G)
    {z : G} (hzL : z ∈ generalizedFitting G) (hz : orderOf z = 2) (hzA : z ∈ A)
    (d : CyclicCoreData (generalizedFitting G) (T : Subgroup G) z)
    (hf : ExceptionalFusion d)
    (hgeometry : ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
      IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) →
      Nat.card F = p ^ 2 → (∀ x, J.conj x = x ^ p) →
      J.form = !![0,0,1;0,1,0;1,0,0] → AbelianOuterCoordinateGeometry J) :
    ∃ g : G,
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      z ∈ A.map (MulAut.conj g).toMonoidHom ∧
      HasInvertedCoordinates (generalizedFitting G)
        ((T : Subgroup G) ⊓ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G))
        ⟨z, hzL⟩ p := by
  exact exists_positioned_inverted_coordinates_of_abelian_reselection hp ho hmodel
    A hout hzL hz (exists_abelian_reselection_of_cyclicCoreData d hf
      A hAT hfour hout hz hzA) hgeometry

/-- Discharge `hselect` in the literal coordinate consumer from the source's
positioned outer four-actor. Only the independent `hgeometry` premise remains. -/
theorem exists_positioned_inverted_coordinates_of_abelian_geometry
    [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hfour : Nat.card A = 4)
    (hout : ¬ A ≤ generalizedFitting G)
    {z : G} (hzL : z ∈ generalizedFitting G) (hz : orderOf z = 2) (hzA : z ∈ A)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hgeometry : ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
      IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) →
      Nat.card F = p ^ 2 → (∀ x, J.conj x = x ^ p) →
      J.form = !![0,0,1;0,1,0;1,0,0] → AbelianOuterCoordinateGeometry J) :
    ∃ g : G,
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      z ∈ A.map (MulAut.conj g).toMonoidHom ∧
      HasInvertedCoordinates (generalizedFitting G)
        ((T : Subgroup G) ⊓ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G))
        ⟨z, hzL⟩ p := by
  exact exists_positioned_inverted_coordinates_of_abelian_reselection hp ho hmodel
    A hout hzL hz (exists_abelian_reselection_of_isPSU hp ho hmod hmodel
      A hAT hfour hout hz hzL hzA hTz) hgeometry

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
