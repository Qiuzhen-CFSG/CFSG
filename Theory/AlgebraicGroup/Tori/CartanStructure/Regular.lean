module

public import Theory.AlgebraicGroup.Tori.CentralMaximalNilpotent
public import Theory.AlgebraicGroup.Tori.RegularCentralizer

/-!
# Cartan structure and a regular torus element

For a maximal torus `T`, the literal subgroup `H = C_G(T)^0` is connected
and nilpotent, hence solvable, and satisfies `N_G(H)^0 = H`. It is also the
identity component of the centralizer of an element of `T`.

The central maximal torus inside `H` supplies nilpotence by the central-torus
quotient argument. Torus rigidity supplies the normalizer equality, while
separating the finitely many weights of a faithful representation supplies
the regular element. These arguments only need connectedness of `H`; ambient
connectedness is unnecessary for this part of the source argument.

Source: Borel, *Linear Algebraic Groups*, second edition,
`refs/KGroup/Bor1/Chapter4.tex`, §§11.5(3)(b⇒c), 11.7, and the first paragraph
of the proof of §11.10; `refs/KGroup/Bor1/Chapter3.tex`, §8.18.
-/

namespace Theory.AlgebraicGroup.CartanStructure

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- The Cartan structure used in Borel §11.10, with nilpotence, the
normalizer equality, and existence of the regular element all proved. -/
public theorem centralizerComponent_structure
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    let H := T.centralizer.identityComponentAmbient
    _root_.IsConnected (H : Set (Variety.Point G)) ∧
      Group.IsNilpotent (Variety.Point H.carrierVariety) ∧
      Group.IsSolvable (Variety.Point H.carrierVariety) ∧
      H.normalizer.identityComponentAmbient = H ∧
      ∃ t : Variety.Point G, t ∈ T.toSubgroup ∧
        (semisimpleCommutatorPointCentralizer t).identityComponentAmbient = H := by
  let H := T.centralizer.identityComponentAmbient
  let : Group.IsNilpotent (Variety.Point H.carrierVariety) :=
    CentralMaximalNilpotent.centralizerComponent_isNilpotent hT
  exact ⟨T.centralizer.identityComponentAmbient_isConnected, inferInstance,
    inferInstance, centralizerComponent_normalizer_identityComponent_eq hT,
    exists_regularTorusElement_identityComponentAmbient_eq hT⟩

end Theory.AlgebraicGroup.CartanStructure
