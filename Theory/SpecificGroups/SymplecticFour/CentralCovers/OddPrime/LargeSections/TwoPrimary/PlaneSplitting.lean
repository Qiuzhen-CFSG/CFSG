module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary.PlaneModel
public import Theory.SpecificGroups.SL2.CentralTwoExtensions

/-!
# Central two-group extensions of the symplectic plane group

The plane group is the actual matrix group SL₂(p). Its central two-group
extensions split for every prime p > 3, including p = 5. This supplies
exactly the splitting premise of `exists_section_on_plane_model`: it applies
to full embedded preimages, without assuming those preimages are perfect.

Source: the rank-one input to the odd type C₂ multiplier calculation in
GLS3 §6.1 and Aschbacher–Smith I.1.1–3, printed p.407. The intrinsic proof
uses cyclic/quaternion Sylow subgroups and central Sylow transfer.
-/

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary

universe u

/-- A section of every finite central two-group extension of the actual
symplectic plane group, with no perfectness assumption on the extension. -/
public theorem exists_plane_section {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    {D : Type u} [Group D] [Finite D] (q : D →* Plane p)
    (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center D)
    (hk : IsPGroup 2 q.ker) :
    ∃ s : Plane p →* D, q.comp s = MonoidHom.id _ :=
  Matrix.SpecialLinearGroup.exists_section_of_central_two_kernel hp q hq hc hk

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary
