module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.CartanGeometry.CommonBorel
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.CartanGeometry.LocalCentralizer
public import Theory.AlgebraicGroup.Tori.Character.ConnectedKernel
public import Theory.AlgebraicGroup.Tori.Maximal.theorem_1_4_3_b


/-!
# Cartan connectedness from the earlier Borel geometry

The complete fixed-locus argument of Borel, *Linear Algebraic Groups*, §11.12
is assembled here for every subtorus. Element coverage (§11.10) gives a common
Borel for the subtorus and each centralizing element. The solvable centralizer
inside that Borel then places the element in the ambient identity component.

The earlier element-coverage statement remains an explicit premise. For a
maximal torus, nilpotence of the identity component (§11.7) is also explicit;
once connectedness is established, it gives the requested solvability of the
full centralizer. These conditional theorems do not assert the unconditional
§11.7 or §11.12 results.

The character-kernel application uses the literal ambient image of `(ker chi)^0`
and preserves its inclusions and codimension from `Character.ConnectedKernel`.
It asserts connectedness of that centralizer only, since such a centralizer
need not be solvable.

Source: `refs/KGroup/Bor1/Chapter4.tex`, §§11.7, 11.10–11.12 and 13.2.
-/

universe u
namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.CartanGeometry
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- The general subtorus-centralizer connectedness deduction in §11.12,
conditional only on the earlier element-coverage theorem. -/
public theorem subtorus_centralizer_isConnected_of_element_coverage
    (hcoverage : ∀ a : Variety.Point G,
      ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ a ∈ B)
    {S : ClosedSubgroup G} (hS : IsSubtorus S) :
    Variety.IsConnected S.centralizer.carrierVariety :=
  centralizer_isConnected_of_common_borels hS
    (exists_common_borel_of_element_coverage hcoverage hS)

/-- Element coverage identifies the actual ambient identity component with
the full subtorus centralizer. -/
public theorem subtorus_centralizer_identityComponent_eq_of_element_coverage
    (hcoverage : ∀ a : Variety.Point G,
      ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ a ∈ B)
    {S : ClosedSubgroup G} (hS : IsSubtorus S) :
    S.centralizer.identityComponentAmbient = S.centralizer :=
  centralizer_identityComponent_eq_of_common_borels hS
    (exists_common_borel_of_element_coverage hcoverage hS)

/-- The maximal-torus package consumed by semisimple center containment.
The two earlier source inputs are element coverage and nilpotence of the
identity component; connectedness of the full centralizer is proved here. -/
public theorem maximalTorus_centralizer_connected_solvable_of_element_coverage_of_identityComponent_nilpotent
    (hcoverage : ∀ a : Variety.Point G,
      ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ a ∈ B)
    {S : ClosedSubgroup G} (hS : IsMaximalTorus S)
    (hnil : Group.IsNilpotent
      (Variety.Point S.centralizer.identityComponentAmbient.carrierVariety)) :
    Variety.IsConnected S.centralizer.carrierVariety ∧
      Group.IsSolvable (Variety.Point S.centralizer.carrierVariety) := by
  refine ⟨subtorus_centralizer_isConnected_of_element_coverage hcoverage hS.1, ?_⟩
  have heq := subtorus_centralizer_identityComponent_eq_of_element_coverage hcoverage hS.1
  rw [heq] at hnil
  let := hnil
  infer_instance

/-- Application to the actual connected kernel of a nontrivial torus character,
including all of its existing codimension-one and inclusion conclusions. -/
public theorem connectedKernel_centralizer_isConnected_of_element_coverage
    (hcoverage : ∀ a : Variety.Point G,
      ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ a ∈ B)
    (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (chi : TorusCharacter T.carrierVariety) (hchi : chi ≠ 1) :
    chi.ConnectedKernelCodimensionOne T ∧
      Variety.IsConnected (chi.ambientConnectedKernel T).centralizer.carrierVariety := by
  have hker := chi.connectedKernel_codimension_one T hT hchi
  exact ⟨hker, subtorus_centralizer_isConnected_of_element_coverage hcoverage
    hker.ambientConnectedKernel_isSubtorus⟩

end Theory.AlgebraicGroup.SemisimpleCenterContainment.CartanGeometry
