module

public import Theory.AlgebraicGroup.Borel.ElementCoverage.Defs
public import Theory.AlgebraicGroup.Borel.ElementCoverage.RegularWitness.Transporter
public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteIndex
public import Theory.AlgebraicGroup.ClosedSubgroup.Normalizer
public import Theory.AlgebraicGroup.Tori.Maximal.theorem_1_4_3_b
public import Theory.AlgebraicGroup.Tori.Semisimple

set_option linter.style.haveILetI false

/-!
# Regular elements and the finite fixed-coset reduction

This file proves the finite-fibre deduction in Borel's argument in
Chapter 4, §11.10. The geometric inputs from §11.7 (nilpotence and equality
with the normalizer's identity component) and §8.18 (choice of a regular
torus element) remain explicit in `exists_witness_of_cartan_inputs`.
The transporter and relative finite-index arguments are proved here and in
`RegularWitness.Transporter`.

The quotient is formed inside the normalizer.  Thus the statement does not
confuse finiteness of the set of conjugates of an element with finiteness of
the fixed points of the actual Plücker homogeneous space.
-/

namespace Theory.AlgebraicGroup.BorelElementCoverage

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

open Bor1

section

variable (H : ClosedSubgroup G)

local notation "N" => H.normalizer.toSubgroup
local notation "K" => H.toSubgroup.subgroupOf N

/-- The quotient of the normalizer by `H`, represented on the actual
homogeneous space. -/
private noncomputable def normalizerQuotientMap :
    Quotient (QuotientGroup.leftRel K) → borelHomogeneousSpace H :=
  @Quotient.lift N (borelHomogeneousSpace H) (QuotientGroup.leftRel K)
    (fun n : N => borelHomogeneousSpace.projection H n.1) (by
    intro a b hab
    apply (borelHomogeneousSpace.projection_eq_iff H a.1 b.1).2
    refine ⟨a.1⁻¹ * b.1, ?_, ?_⟩
    · have hab' : a⁻¹ * b ∈ K :=
        (QuotientGroup.leftRel_apply (s := K) (x := a) (y := b)).mp hab
      exact hab'
    · simp)

end

/--
If every fixed homogeneous-space point has a representative in the
normalizer, then the fixed-point set is finite as soon as `H` has finite index
in its normalizer.  This is the component quotient occurring in Borel's
argument; `H` need not have finite index in the ambient group.  The quotient
is represented by `H.subgroupOf H.normalizer`.

This is the reusable §11.10 reduction.  A Cartan-structure theorem only has to
provide the transporter assertion; no completeness or Borel self-normalizing
claim is used here.
-/
public theorem finite_fixedCosets_of_normalizer_transporter
    (H : ClosedSubgroup G) (h : Variety.Point G)
    (hindex :
      (H.toSubgroup.subgroupOf H.normalizer.toSubgroup).FiniteIndex)
    (htrans : ∀ g : Variety.Point G,
      h • borelHomogeneousSpace.projection H g =
          borelHomogeneousSpace.projection H g →
      ∃ n : H.normalizer.toSubgroup,
        borelHomogeneousSpace.projection H g =
          borelHomogeneousSpace.projection H n.1) :
    Set.Finite {q : borelHomogeneousSpace H | h • q = q} := by
  let N : Subgroup (Variety.Point G) := H.normalizer.toSubgroup
  let K : Subgroup N := H.toSubgroup.subgroupOf N
  let f : Quotient (QuotientGroup.leftRel K) → borelHomogeneousSpace H :=
    normalizerQuotientMap H
  have hquot : Finite (Quotient (QuotientGroup.leftRel K)) := by
    letI : K.FiniteIndex := hindex
    exact Subgroup.finite_quotient_of_finiteIndex
  have hfrange : (Set.range f).Finite := by
    exact @Set.finite_range _ _ f hquot
  apply hfrange.subset
  intro q hq
  obtain ⟨g, rfl⟩ := borelHomogeneousSpace.projection_surjective H q
  obtain ⟨n, hn⟩ := htrans g hq
  refine ⟨(@Quotient.mk' _ (QuotientGroup.leftRel K) n), ?_⟩
  change borelHomogeneousSpace.projection H n.1 =
    borelHomogeneousSpace.projection H g
  exact hn.symm

/-- A compact package of the hypotheses used by the finite fixed-coset
reduction.  It is convenient when the regular element and its transporter are
constructed together with the Cartan subgroup. -/
public structure RegularFixedCosetData (H : ClosedSubgroup G) where
  element : Variety.Point G
  element_mem : element ∈ H.toSubgroup
  finiteIndex :
    (H.toSubgroup.subgroupOf H.normalizer.toSubgroup).FiniteIndex
  transporter : ∀ g : Variety.Point G,
    element • borelHomogeneousSpace.projection H g =
        borelHomogeneousSpace.projection H g →
    ∃ n : H.normalizer.toSubgroup,
      borelHomogeneousSpace.projection H g =
        borelHomogeneousSpace.projection H n.1

/-- The packaged form of `finite_fixedCosets_of_normalizer_transporter`. -/
public theorem RegularFixedCosetData.finite_fixedCosets
    {H : ClosedSubgroup G} (d : RegularFixedCosetData H) :
    Set.Finite {q : borelHomogeneousSpace H | d.element • q = q} := by
  exact finite_fixedCosets_of_normalizer_transporter H d.element d.finiteIndex d.transporter

/-- The exact existential endpoint needed by the density argument, once the
Cartan construction has supplied its connected solvable subgroup and regular
fixed-coset data. -/
public structure ConnectedSolvableRegularWitnessData where
  subgroup : ClosedSubgroup G
  connected : _root_.IsConnected (subgroup : Set (Variety.Point G))
  solvable : Group.IsSolvable (Variety.Point subgroup.carrierVariety)
  regular : RegularFixedCosetData subgroup

public theorem ConnectedSolvableRegularWitnessData.exists_witness
    (d : ConnectedSolvableRegularWitnessData (G := G)) :
    ∃ H : ClosedSubgroup G,
      _root_.IsConnected (H : Set (Variety.Point G)) ∧
      Group.IsSolvable (Variety.Point H.carrierVariety) ∧
      ∃ h : Variety.Point G, h ∈ H.toSubgroup ∧
        Set.Finite {q : borelHomogeneousSpace H | h • q = q} := by
  refine ⟨d.subgroup, d.connected, d.solvable, d.regular.element, ?_, ?_⟩
  · exact d.regular.element_mem
  · exact d.regular.finite_fixedCosets

/-- A regular semisimple element in a nilpotent connected subgroup has
finitely many fixed cosets if the normalizer has no larger identity component.
Both the transporter and the finite component quotient are deduced, rather
than supplied as fixed-coset hypotheses. -/
public theorem finite_fixedCosets_of_nilpotent_regular
    (H : ClosedSubgroup G)
    (hnil : Group.IsNilpotent (Variety.Point H.carrierVariety))
    (hnormalizer : H.normalizer.identityComponentAmbient ≤ H)
    (t : Variety.Point G) (ht : IsSemisimpleElement G t)
    (hregular : (semisimpleCommutatorPointCentralizer t).identityComponentAmbient = H) :
    Set.Finite {q : borelHomogeneousSpace H | t • q = q} := by
  have hH : _root_.IsConnected (H : Set (Variety.Point G)) := by
    rw [← hregular]
    exact ClosedSubgroup.identityComponentAmbient_isConnected _
  apply finite_fixedCosets_of_normalizer_transporter H t
    (finiteIndex_subgroupOf_of_identityComponentAmbient_le H H.normalizer hnormalizer)
  intro g hfixed
  have hg : g⁻¹ * t * g ∈ H.toSubgroup :=
    (H.mem_conjugate_iff g t).mp
      ((Bor1.projectivization_fixed_iff_mem_conjugate H g t).mp
        (congrArg Subtype.val hfixed))
  exact ⟨⟨g, transporter_mem_normalizer_of_regular_semisimple
    H hH hnil t ht hregular g hg⟩, rfl⟩

/-- The literal Cartan application in §11.10. The remaining source inputs
are §11.7 for `C_G(T)°` and the centralizer equality from §8.18. This is a
conditional assembly, not an unconditional Cartan existence theorem. -/
public theorem exists_witness_of_cartan_inputs
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hnil : Group.IsNilpotent
      (Variety.Point T.centralizer.identityComponentAmbient.carrierVariety))
    (hnormalizer : T.centralizer.identityComponentAmbient.normalizer.identityComponentAmbient ≤
      T.centralizer.identityComponentAmbient)
    (hregular : ∃ t : Variety.Point G, t ∈ T.toSubgroup ∧
      (semisimpleCommutatorPointCentralizer t).identityComponentAmbient =
        T.centralizer.identityComponentAmbient) :
    ∃ H : ClosedSubgroup G,
      _root_.IsConnected (H : Set (Variety.Point G)) ∧
      Group.IsSolvable (Variety.Point H.carrierVariety) ∧
      ∃ h : Variety.Point G, h ∈ H.toSubgroup ∧
        Set.Finite {q : borelHomogeneousSpace H | h • q = q} := by
  obtain ⟨t, htT, htreg⟩ := hregular
  let H := T.centralizer.identityComponentAmbient
  let : Group.IsNilpotent (Variety.Point H.carrierVariety) := hnil
  have htH : t ∈ H.toSubgroup :=
    maximalTorus_le_identityComponentAmbient_of_le T T.centralizer hT
      (maximalTorus_le_centralizer hT) htT
  have htsemi : IsSemisimpleElement G t :=
    (closedSubgroup_semisimpleElement_iff T htT).mpr
      (hT.1.all_semisimple (T.pointEquiv.symm ⟨t, htT⟩))
  exact ⟨H, T.centralizer.identityComponentAmbient_isConnected, inferInstance,
    t, htH, finite_fixedCosets_of_nilpotent_regular H hnil hnormalizer t htsemi htreg⟩

end Theory.AlgebraicGroup.BorelElementCoverage
