module

public import Theory.AlgebraicGroup.Borel.ElementCoverage.RegularWitness.FixedCosets
public import Theory.AlgebraicGroup.Tori.CartanStructure.Regular

/-!
# Cartan structure and regular fixed cosets

Borel, *Linear Algebraic Groups*, §§11.7 and 11.10. The normalizer component
is computed in `Tori.CartanStructure`. This file applies that equality to the
literal normalizer quotient and the left-coset transporter from
`RegularWitness.Transporter`, constructing `RegularFixedCosetData`.

The conditional constructors are retained. The terminal constructor supplies
nilpotence of the centralizer component (§11.5(3)(b⇒c) applied as in §11.7)
and the regular point (§8.18), using `Tori.CartanStructure.Regular`. It yields
the actual finite fixed-coset witness with no additional source premises.

Source: `refs/KGroup/Bor1/Chapter4.tex`, §§11.5, 11.7, 11.10, and
`refs/KGroup/Bor1/Chapter3.tex`, §8.18.
-/

namespace Theory.AlgebraicGroup.BorelElementCoverage

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- A nilpotent Cartan component and an actual regular torus point supply
the finite-index and transporter fields, using the proved §11.7 normalizer
identity rather than taking that identity as an additional input. -/
public noncomputable def regularFixedCosetData_of_nilpotent_of_regular
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T)
    (hnil : Group.IsNilpotent
      (Variety.Point T.centralizer.identityComponentAmbient.carrierVariety))
    (t : Variety.Point G) (htT : t ∈ T.toSubgroup)
    (hregular : (semisimpleCommutatorPointCentralizer t).identityComponentAmbient =
      T.centralizer.identityComponentAmbient) :
    RegularFixedCosetData T.centralizer.identityComponentAmbient := by
  let H := T.centralizer.identityComponentAmbient
  have hn : H.normalizer.identityComponentAmbient ≤ H := by
    rw [CartanStructure.centralizerComponent_normalizer_identityComponent_eq hT]
    exact fun _ hx => hx
  have ht : IsSemisimpleElement G t :=
    (closedSubgroup_semisimpleElement_iff T htT).mpr
      (hT.1.all_semisimple (T.pointEquiv.symm ⟨t, htT⟩))
  refine
    { element := t
      element_mem := maximalTorus_le_identityComponentAmbient_of_le
        T T.centralizer hT (maximalTorus_le_centralizer hT) htT
      finiteIndex := finiteIndex_subgroupOf_of_identityComponentAmbient_le H H.normalizer hn
      transporter := ?_ }
  intro g hfixed
  have hg : g⁻¹ * t * g ∈ H.toSubgroup :=
    (H.mem_conjugate_iff g t).mp
      ((Bor1.projectivization_fixed_iff_mem_conjugate H g t).mp
        (congrArg Subtype.val hfixed))
  exact ⟨⟨g, transporter_mem_normalizer_of_regular_semisimple
    H T.centralizer.identityComponentAmbient_isConnected hnil t ht hregular g hg⟩, rfl⟩

/-- The actual connected-solvable fixed-coset witness, with only the earlier
nilpotence and regular-point source inputs left to be supplied. -/
public theorem exists_witness_of_nilpotent_of_regular
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T)
    (hnil : Group.IsNilpotent
      (Variety.Point T.centralizer.identityComponentAmbient.carrierVariety))
    (hregular : ∃ t : Variety.Point G, t ∈ T.toSubgroup ∧
      (semisimpleCommutatorPointCentralizer t).identityComponentAmbient =
        T.centralizer.identityComponentAmbient) :
    ∃ H : ClosedSubgroup G,
      _root_.IsConnected (H : Set (Variety.Point G)) ∧
      Group.IsSolvable (Variety.Point H.carrierVariety) ∧
      ∃ h : Variety.Point G, h ∈ H.toSubgroup ∧
        Set.Finite {q : Bor1.borelHomogeneousSpace H | h • q = q} := by
  obtain ⟨t, ht, hreg⟩ := hregular
  let : Group.IsNilpotent
      (Variety.Point T.centralizer.identityComponentAmbient.carrierVariety) := hnil
  let d : ConnectedSolvableRegularWitnessData (G := G) :=
    { subgroup := T.centralizer.identityComponentAmbient
      connected := T.centralizer.identityComponentAmbient_isConnected
      solvable := inferInstance
      regular := regularFixedCosetData_of_nilpotent_of_regular hT hnil t ht hreg }
  exact d.exists_witness

/-- The regular point required by §8.18 is supplied by the finite-weight
construction in `Tori.RegularCentralizer`. -/
public theorem exists_witness_of_nilpotent_of_maximalTorus
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T)
    (hnil : Group.IsNilpotent
      (Variety.Point T.centralizer.identityComponentAmbient.carrierVariety)) :
    ∃ H : ClosedSubgroup G,
      _root_.IsConnected (H : Set (Variety.Point G)) ∧
      Group.IsSolvable (Variety.Point H.carrierVariety) ∧
      ∃ h : Variety.Point G, h ∈ H.toSubgroup ∧
        Set.Finite {q : Bor1.borelHomogeneousSpace H | h • q = q} := by
  exact exists_witness_of_nilpotent_of_regular hT hnil
    (exists_regularTorusElement_identityComponentAmbient_eq hT)

/-- Application of the earlier universal §11.5(3)(b⇒c) statement to the
literal centralizer component. The central maximal torus is constructed by
`CartanStructure`; the earlier source theorem and the §8.18 point witness
remain explicit for final assembly. -/
public theorem exists_witness_of_central_maximal_nilpotence_of_regular
    (hnil : ∀ (K : Variety k) [AlgebraicGroup K], Variety.IsConnected K →
      ∀ S : ClosedSubgroup K, IsMaximalTorus S →
        S.toSubgroup ≤ Subgroup.center (Variety.Point K) →
        Group.IsNilpotent (Variety.Point K))
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T)
    (hregular : ∃ t : Variety.Point G, t ∈ T.toSubgroup ∧
      (semisimpleCommutatorPointCentralizer t).identityComponentAmbient =
        T.centralizer.identityComponentAmbient) :
    ∃ H : ClosedSubgroup G,
      _root_.IsConnected (H : Set (Variety.Point G)) ∧
      Group.IsSolvable (Variety.Point H.carrierVariety) ∧
      ∃ h : Variety.Point G, h ∈ H.toSubgroup ∧
        Set.Finite {q : Bor1.borelHomogeneousSpace H | h • q = q} := by
  let H := T.centralizer.identityComponentAmbient
  have hH : Variety.IsConnected H.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
    let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
      Subtype.connectedSpace T.centralizer.identityComponentAmbient_isConnected
    let : ConnectedSpace (Variety.Point H.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  obtain ⟨S, hS, hcentral, _himage⟩ :=
    CartanStructure.exists_central_maximalTorus_in_centralizerComponent hT
  exact exists_witness_of_nilpotent_of_regular hT
    (hnil H.carrierVariety hH S hS hcentral) hregular

/-- Construct the regular fixed-coset data for the literal Cartan component.
Both earlier source inputs are discharged: nilpotence by §11.5 and the
regular point by the finite-weight construction of §8.18. -/
public noncomputable def regularFixedCosetData_of_maximalTorus
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    RegularFixedCosetData T.centralizer.identityComponentAmbient := by
  let hex := exists_regularTorusElement_centralizer_eq hT
  exact regularFixedCosetData_of_nilpotent_of_regular hT
    (CentralMaximalNilpotent.centralizerComponent_isNilpotent hT)
    (Classical.choose hex) (Classical.choose_spec hex).1
    (congrArg ClosedSubgroup.identityComponentAmbient (Classical.choose_spec hex).2)

/-- The constructed point lies in the original torus and even has the same
full centralizer as that torus. No full-centralizer connectedness is asserted. -/
public theorem regularFixedCosetData_of_maximalTorus_spec
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    let t := (regularFixedCosetData_of_maximalTorus hT).element
    t ∈ T.toSubgroup ∧ semisimpleCommutatorPointCentralizer t = T.centralizer := by
  exact Classical.choose_spec (exists_regularTorusElement_centralizer_eq hT)

/-- The regular element of the original torus has finitely many fixed points
on the actual left homogeneous space of `C_G(T)^0`. This is the hypothesis
of Borel §11.9(2) used in §11.10. -/
public theorem exists_regularTorusElement_finite_fixedCosets
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    ∃ t : Variety.Point G, t ∈ T.toSubgroup ∧
      (semisimpleCommutatorPointCentralizer t).identityComponentAmbient =
        T.centralizer.identityComponentAmbient ∧
      Set.Finite {q : Bor1.borelHomogeneousSpace T.centralizer.identityComponentAmbient |
        t • q = q} := by
  let d := regularFixedCosetData_of_maximalTorus hT
  obtain ⟨ht, hcentral⟩ := regularFixedCosetData_of_maximalTorus_spec hT
  exact ⟨d.element, ht, congrArg ClosedSubgroup.identityComponentAmbient hcentral,
    d.finite_fixedCosets⟩

/-- A maximal torus supplies the connected solvable witness required by the
density argument. The subgroup is literally `C_G(T)^0`. -/
public theorem exists_witness_of_maximalTorus
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    ∃ H : ClosedSubgroup G,
      _root_.IsConnected (H : Set (Variety.Point G)) ∧
      Group.IsSolvable (Variety.Point H.carrierVariety) ∧
      ∃ h : Variety.Point G, h ∈ H.toSubgroup ∧
        Set.Finite {q : Bor1.borelHomogeneousSpace H | h • q = q} := by
  obtain ⟨hconnected, _hnil, hsolvable, _hnormalizer, _hregular⟩ :=
    CartanStructure.centralizerComponent_structure hT
  let d : ConnectedSolvableRegularWitnessData (G := G) :=
    { subgroup := T.centralizer.identityComponentAmbient
      connected := hconnected
      solvable := hsolvable
      regular := regularFixedCosetData_of_maximalTorus hT }
  exact d.exists_witness

/-- Existence of the connected solvable regular witness, with a maximal
torus chosen by dimension. This discharges all Cartan inputs of the
finite fixed-coset reduction. -/
public theorem exists_connectedSolvable_regularWitness (G : Variety k) [AlgebraicGroup G] :
    ∃ H : ClosedSubgroup G,
      _root_.IsConnected (H : Set (Variety.Point G)) ∧
      Group.IsSolvable (Variety.Point H.carrierVariety) ∧
      ∃ h : Variety.Point G, h ∈ H.toSubgroup ∧
        Set.Finite {q : Bor1.borelHomogeneousSpace H | h • q = q} := by
  obtain ⟨T, hT⟩ := exists_maximalTorus G
  exact exists_witness_of_maximalTorus hT

end Theory.AlgebraicGroup.BorelElementCoverage
