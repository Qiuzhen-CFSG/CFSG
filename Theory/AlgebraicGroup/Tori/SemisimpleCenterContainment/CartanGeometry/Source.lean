module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.CartanGeometry
public import Theory.AlgebraicGroup.Tori.CentralMaximalNilpotent
public import Theory.AlgebraicGroup.Borel.ElementCoverage.Source

/-!
# Connected torus centralizers and solvable Cartan subgroups

Every element of the original connected group lies in a Borel conjugate.
The complete fixed-locus argument therefore places every point centralizing
an arbitrary subtorus in the identity component of that centralizer. For a
maximal torus the previously constructed centralizer component is nilpotent,
so the full centralizer is nilpotent, and in particular solvable.

These are Borel, *Linear Algebraic Groups*, IV, §§11.7 and 11.12. No Borel
coverage or component-nilpotence premise remains. This supplies the Cartan
input to GLS3 Theorem 1.9.5(h); radical torality is a separate source step.
-/

public section
namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.CartanGeometry
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

private theorem exists_borel_containing_point (hG : Variety.IsConnected G)
    (x : Variety.Point G) : ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ x ∈ B := by
  obtain ⟨B,hB⟩ := exists_borelSubgroup G
  obtain ⟨g,hg⟩ := BorelElementCoverage.exists_conjugate_mem hG hB x
  exact ⟨B.conjugate g,hB.conjugate g,(B.mem_conjugate_iff g x).mpr hg⟩

/-- Borel IV, 11.12: the centralizer of every subtorus in a connected
algebraic group is connected. -/
theorem subtorus_centralizer_isConnected (hG : Variety.IsConnected G)
    {S : ClosedSubgroup G} (hS : IsSubtorus S) :
    Variety.IsConnected S.centralizer.carrierVariety :=
  subtorus_centralizer_isConnected_of_element_coverage
    (exists_borel_containing_point hG) hS

/-- The actual ambient centralizer component is the full centralizer. -/
theorem subtorus_centralizer_identityComponent_eq (hG : Variety.IsConnected G)
    {S : ClosedSubgroup G} (hS : IsSubtorus S) :
    S.centralizer.identityComponentAmbient = S.centralizer :=
  subtorus_centralizer_identityComponent_eq_of_element_coverage
    (exists_borel_containing_point hG) hS

/-- Borel IV, 11.7 and 11.12: the full centralizer of a maximal torus is
nilpotent, after identifying it with its actual identity component. -/
theorem maximalTorus_centralizer_isNilpotent (hG : Variety.IsConnected G)
    {S : ClosedSubgroup G} (hS : IsMaximalTorus S) :
    Group.IsNilpotent (Variety.Point S.centralizer.carrierVariety) := by
  have hn := CentralMaximalNilpotent.centralizerComponent_isNilpotent hS
  rwa [subtorus_centralizer_identityComponent_eq hG hS.1] at hn

/-- The exact Cartan package used by semisimple center containment, with all
of its earlier source geometry discharged. -/
theorem maximalTorus_centralizer_connected_solvable (hG : Variety.IsConnected G)
    {S : ClosedSubgroup G} (hS : IsMaximalTorus S) :
    Variety.IsConnected S.centralizer.carrierVariety ∧
      Group.IsSolvable (Variety.Point S.centralizer.carrierVariety) := by
  let := maximalTorus_centralizer_isNilpotent hG hS
  exact ⟨subtorus_centralizer_isConnected hG hS.1,inferInstance⟩

/-- The same source theorem applies to the literal connected character
kernel used by the rank-one centralizer constructions. -/
theorem connectedKernel_centralizer_isConnected (hG : Variety.IsConnected G)
    (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (chi : TorusCharacter T.carrierVariety) (hchi : chi ≠ 1) :
    chi.ConnectedKernelCodimensionOne T ∧
      Variety.IsConnected (chi.ambientConnectedKernel T).centralizer.carrierVariety :=
  connectedKernel_centralizer_isConnected_of_element_coverage
    (exists_borel_containing_point hG) T hT chi hchi

end Theory.AlgebraicGroup.SemisimpleCenterContainment.CartanGeometry
