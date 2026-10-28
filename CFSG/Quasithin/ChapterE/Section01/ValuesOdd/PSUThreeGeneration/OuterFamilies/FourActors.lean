module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.Obstruction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.ModelInputs
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.Reduction

/-!
# The positioned order-four branch of the PSU₃ obstruction

The whole family actor can now be positioned with its inner involution central
in the fixed Sylow subgroup. Local structure on the centralizer's residual
supplement then traps the full centralizer in the obstruction overgroup.

The assembly below still takes the outer local structure and the subsequent
unitary generation argument as explicit hypotheses. It is not the unconditional
order-four exclusion. Those two inputs can be proved independently: the latter
may assume the centralizer containment established from the former. Final
discharge and the unconditional theorem belong in this module.

Source: Aschbacher--Smith, E.1.14(7), printed p.214; E.1.1--2 and E.1.5,
printed pp.209--210; Aschbacher, *GF(2)-representations of finite groups*
(1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors
variable {G : Type*} [Group G] [Finite G]

/-- Conditional assembly: all positioning, E₀, quotient-rank and solvable
supplement premises have been discharged. The two remaining model inputs
are stated only for the actual positioned family actor. -/
theorem no_large_obstruction_of_four_actor_of_centralizer_inputs
    (L : Subgroup G) [L.Normal] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p)
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    {A : Subgroup G} (hA : A ∈ d.family)
    (hfour : Nat.card A = 4) (hinter : Nat.card (A ⊓ L : Subgroup G) = 2)
    (hlocal : ∀ B ∈ d.family, B ≤ (T : Subgroup G) → B ≠ ⊥ →
      Nat.card B = 4 → Nat.card (B ⊓ L : Subgroup G) = 2 →
      ∀ z : G, orderOf z = 2 → z ∈ L → z ∈ B →
        (T : Subgroup G) ≤ centralizer ({z} : Set G) →
        Group.IsSolvable (centralizer ({z} : Set G)) ∨
          ECaseOdd B (centralizerResidualOvergroup T z) ∨
          ECaseComponent (T : Subgroup G) B (centralizerResidualOvergroup T z))
    (hgeometry : ∀ B ∈ d.family, B ≤ (T : Subgroup G) → B ≠ ⊥ →
      Nat.card B = 4 → Nat.card (B ⊓ L : Subgroup G) = 2 →
      ∀ z : G, orderOf z = 2 → z ∈ L → z ∈ B →
        (T : Subgroup G) ≤ centralizer ({z} : Set G) →
        centralizer ({z} : Set G) ≤ d.overgroup → False) : False := by
  obtain ⟨B, hB, hBT, hne, hcard, hinner, z, hz, hzL, hzB, hTz⟩ :=
    exists_positioned_four_actor L hp ho hmodel d hA hfour hinter
  have hz1 : z ≠ 1 := by
    intro h
    simp [h] at hz
  have hCM := centralizer_le_of_local_structure d hB hBT hcard hzB hz1 hTz
    (hlocal B hB hBT hne hcard hinner z hz hzL hzB hTz)
  exact hgeometry B hB hBT hne hcard hinner z hz hzL hzB hTz hCM

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors
