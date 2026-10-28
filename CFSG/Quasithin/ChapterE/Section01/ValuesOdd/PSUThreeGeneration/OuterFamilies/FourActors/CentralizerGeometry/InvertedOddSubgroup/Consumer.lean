module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry

/-!
# Application of the concrete witnesses to the congruence assembly

The root/rotation construction supplies precisely the normalized, inverted
odd subgroup requested by the `hone` premise of the congruence assembly.
Intrinsic centralizer maximality, the p congruent to three construction and
existence of coordinates remain explicit. Keeping this application separate
lets the parent assembly import the construction without an import cycle.

Source: Aschbacher--Smith E.1.14(7), printed p.214, and its cited
Aschbacher (1982), Lemma 4.11; the local E-member calculation is in
`CentralizerGeometry.Reduction`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
variable {G : Type*} [Group G] [Finite G]

/-- Actual application to the congruence assembly; maximality and placement stay explicit. -/
theorem false_of_positioned_coordinates [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (d : LargeFamilyObstruction T) {A : Subgroup G} (hA : A ∈ d.family)
    {z : G} (hzL : z ∈ generalizedFitting G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hCM : centralizer ({z} : Set G) ≤ d.overgroup)
    (hmax : IsCoatom ((centralizer ({z} : Set G)).subgroupOf (generalizedFitting G)))
    (hthree : p % 4 = 3 → ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧
      Group.IsSolvable H ∧ ¬ H ≤ centralizer ({z} : Set G))
    (hcoords : p % 4 = 1 → ∃ g : G,
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      z ∈ A.map (MulAut.conj g).toMonoidHom ∧
      HasInvertedCoordinates (generalizedFitting G)
        ((T : Subgroup G) ⊓ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G))
        ⟨z, hzL⟩ p) : False := by
  exact false_of_congruence_constructions hp ho hmodel hLT d hA hTz hCM hmax hthree
    (fun hm => exists_conjugate_inverted_odd_subgroup_of_coordinates hzL hp ho hm (hcoords hm))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
