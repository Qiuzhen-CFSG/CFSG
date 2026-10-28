module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.Algebra

/-!
The actual intersection subgroups in Borel, Chapter IV, 13.16.

We retain `I(A) = (⋂ {B | B is Borel and A ≤ B})⁰`, including when
`A = B^S` is not a torus. Monotonicity of this intersection puts `I(T)_u`
inside the connected unipotent group `(I(B^S) ∩ B_u)⁰` used in the source.
The fixed-subgroup containment below transfers the geometric conclusion of
13.15(2) to this group. It does not assert that geometric conclusion.
-/

universe u

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The single earlier geometric theorem allowed as input to the normality
argument: restriction of a Borel to a connected subtorus centralizer. -/
public abbrev UniformSubtorusBorelRestriction (k : Type u) [Field k] : Prop :=
  ∀ (G : Variety k) [AlgebraicGroup G], Variety.IsConnected G →
    ∀ S : ClosedSubgroup G, IsSubtorus S →
      Variety.IsConnected S.centralizer.carrierVariety →
      ∀ B : ClosedSubgroup G, IsBorelSubgroup B → S ≤ B →
        IsBorelSubgroup (S.centralizer.inclusion.closedSubgroupPreimage B)

omit [IsAlgClosed k] in
/-- Every member of the defining family contains the Borel intersection. -/
public theorem borelIntersection_le_borel
    {G : Variety k} [AlgebraicGroup G] (A B : ClosedSubgroup G)
    (hB : IsBorelSubgroup B) (hAB : A ≤ B) : borelIntersection A ≤ B := by
  change (borelIntersection A).toSubgroup ≤ B.toSubgroup
  rw [borelIntersection_toSubgroup]
  exact iInf_le (fun D : BorelContainingIndex A => D.1.toSubgroup) ⟨B, hB, hAB⟩

/-- The identity-component intersection lies in each defining Borel. -/
public theorem torusBorelIntersection_le_borel
    {G : Variety k} [AlgebraicGroup G] (A B : ClosedSubgroup G)
    (hB : IsBorelSubgroup B) (hAB : A ≤ B) : torusBorelIntersection A ≤ B := by
  rw [torusBorelIntersection_eq_identityComponentAmbient]
  intro x hx
  exact borelIntersection_le_borel A B hB hAB
    ((borelIntersection A).identityComponentAmbient_le hx)

/-- Increasing the subgroup decreases the family of Borels being intersected. -/
public theorem torusBorelIntersection_mono
    {G : Variety k} [AlgebraicGroup G] {A D : ClosedSubgroup G} (hAD : A ≤ D) :
    torusBorelIntersection A ≤ torusBorelIntersection D := by
  rw [torusBorelIntersection_eq_identityComponentAmbient D]
  apply connected_closedSubgroup_le_identityComponentAmbient
  · rw [torusBorelIntersection_eq_identityComponentAmbient]
    exact (borelIntersection A).identityComponentAmbient_isConnected
  · apply le_borelIntersection_of_forall
    intro B hB hDB
    exact torusBorelIntersection_le_borel A B hB (fun _ hx => hDB (hAD hx))

/-- A connected subgroup contained in `A` lies in `I(A)`. -/
public theorem connected_le_torusBorelIntersection
    {G : Variety k} [AlgebraicGroup G] (V A : ClosedSubgroup G)
    (hVc : _root_.IsConnected (V : Set (Variety.Point G))) (hVA : V ≤ A) :
    V ≤ torusBorelIntersection A := by
  rw [torusBorelIntersection_eq_identityComponentAmbient]
  apply connected_closedSubgroup_le_identityComponentAmbient V _ hVc
  exact le_borelIntersection_of_forall V A (fun _ _ hAB _ hx => hAB (hVA hx))

/-- In particular, a torus lies in its Borel intersection. -/
public theorem torus_le_torusBorelIntersection
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G) (hT : IsSubtorus T) :
    T ≤ torusBorelIntersection T := by
  have hTc : _root_.IsConnected (T : Set (Variety.Point G)) := by
    let : ConnectedSpace (Variety.Point T.carrierVariety) :=
      connectedSpace_iff_univ.mpr hT.isConnected
    change _root_.IsConnected (T.toSubgroup : Set (Variety.Point G))
    rw [← T.range_inclusion]
    exact isConnected_range T.inclusion.toVariety.continuous
  exact connected_le_torusBorelIntersection T T hTc (fun _ hx => hx)

/-- The radical in the task contract is connected, even though the predicate
`IsUnipotentRadicalOf` itself does not require connectedness. -/
public theorem intersection_radical_isConnected
    {G : Variety k} [AlgebraicGroup G] (T U : ClosedSubgroup G)
    (hT : IsSubtorus T) (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U) :
    _root_.IsConnected (U : Set (Variety.Point G)) := by
  obtain ⟨hIc, hIs⟩ := torusBorelIntersection_connected_solvable T hT
  obtain ⟨V, hV, hVc⟩ := exists_unipotentRadical_of_connected_solvable
    (torusBorelIntersection T) hIc hIs
  exact unipotent_radical_unique hV hU ▸ hVc

/-- `I(T)_u` lies in the unipotent radical of every Borel containing `T`. -/
public theorem intersection_radical_le_borel_radical
    {G : Variety k} [AlgebraicGroup G] (T U B V : ClosedSubgroup G)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (hB : IsBorelSubgroup B) (hTB : T ≤ B) (hV : IsUnipotentRadicalOf B V) :
    U ≤ V := by
  exact hV.contains_unipotent_closedSubgroup hB.connected hB.solvable
    (fun _ hx => torusBorelIntersection_le_borel T B hB hTB (hU.1 hx)) hU.2.1

/-- The source's auxiliary group, with `A = B^S` and `V = B_u`. -/
@[expose]
public noncomputable def unipotentEnvelope
    {G : Variety k} [AlgebraicGroup G] (A V : ClosedSubgroup G) : ClosedSubgroup G :=
  ((torusBorelIntersection A).inter V).identityComponentAmbient

/-- The radical of `I(T)` lies in the source's auxiliary group. -/
public theorem intersection_radical_le_unipotentEnvelope
    {G : Variety k} [AlgebraicGroup G] (T U A B V : ClosedSubgroup G)
    (hT : IsSubtorus T) (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (hTA : T ≤ A) (hAB : A ≤ B) (hB : IsBorelSubgroup B)
    (hV : IsUnipotentRadicalOf B V) : U ≤ unipotentEnvelope A V := by
  apply connected_closedSubgroup_le_identityComponentAmbient
    U ((torusBorelIntersection A).inter V)
    (intersection_radical_isConnected T U hT hU)
  intro x hx
  exact (ClosedSubgroup.mem_inter_iff _ _ x).mpr
    ⟨torusBorelIntersection_mono hTA (hU.1 hx),
      intersection_radical_le_borel_radical T U B V hU hB
        (fun _ ht => hAB (hTA ht)) hV hx⟩

/-- The connected fixed unipotent subgroup lies in the auxiliary group
whenever it lies in both `A` and `V`. -/
public theorem connected_le_unipotentEnvelope
    {G : Variety k} [AlgebraicGroup G] (W A V : ClosedSubgroup G)
    (hWc : _root_.IsConnected (W : Set (Variety.Point G)))
    (hWA : W ≤ A) (hWV : W ≤ V) : W ≤ unipotentEnvelope A V := by
  apply connected_closedSubgroup_le_identityComponentAmbient W _ hWc
  intro x hx
  exact (ClosedSubgroup.mem_inter_iff _ _ x).mpr
    ⟨connected_le_torusBorelIntersection W A hWc hWA hx, hWV hx⟩

/-- Unipotence passes to an ambient closed subgroup contained in a unipotent
closed subgroup, retaining the ambient inclusions. -/
public theorem unipotent_of_le
    {G : Variety k} [AlgebraicGroup G] {W V : ClosedSubgroup G}
    (hWV : W ≤ V) (hV : IsUnipotentAlgebraicGroup V.carrierVariety) :
    IsUnipotentAlgebraicGroup W.carrierVariety := by
  intro w
  have hw : (W.pointEquiv w).val ∈ V := hWV (W.pointEquiv w).property
  have hv := hV (V.pointEquiv.symm ⟨(W.pointEquiv w).val, hw⟩)
  apply (closedSubgroup_unipotentElement_iff W (W.pointEquiv w).property).mp
  exact (closedSubgroup_unipotentElement_iff V hw).mpr hv

/-- The auxiliary group is connected and unipotent. -/
public theorem unipotentEnvelope_connected_unipotent
    {G : Variety k} [AlgebraicGroup G] (A V : ClosedSubgroup G)
    (hV : IsUnipotentAlgebraicGroup V.carrierVariety) :
    _root_.IsConnected (unipotentEnvelope A V : Set (Variety.Point G)) ∧
      IsUnipotentAlgebraicGroup (unipotentEnvelope A V).carrierVariety := by
  refine ⟨ClosedSubgroup.identityComponentAmbient_isConnected _, ?_⟩
  apply unipotent_of_le (V := V) _ hV
  intro x hx
  exact ((ClosedSubgroup.mem_inter_iff _ _ x).mp
    (((torusBorelIntersection A).inter V).identityComponentAmbient_le hx)).2

/-- The geometric inclusion of 13.15(2) puts the corresponding fixed subgroup
of the auxiliary unipotent group in `I(T)_u`. -/
public theorem unipotentEnvelope_fixed_le_radical
    {G : Variety k} [AlgebraicGroup G] (T U A V Q : ClosedSubgroup G)
    (hT : IsSubtorus T) (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (hV : IsUnipotentAlgebraicGroup V.carrierVariety)
    (hfixed : (torusBorelIntersection A).pointwiseCentralizer Q ≤
      torusBorelIntersection T) :
    (unipotentEnvelope A V).pointwiseCentralizer Q ≤ U := by
  obtain ⟨hIc, hIs⟩ := torusBorelIntersection_connected_solvable T hT
  apply hU.contains_unipotent_closedSubgroup hIc hIs
  · intro x hx
    obtain ⟨hxH, hxQ⟩ := (ClosedSubgroup.mem_inter_iff _ _ x).mp hx
    have hxI := ((ClosedSubgroup.mem_inter_iff _ _ x).mp
      (((torusBorelIntersection A).inter V).identityComponentAmbient_le hxH)).1
    exact hfixed ((ClosedSubgroup.mem_inter_iff _ _ x).mpr ⟨hxI, hxQ⟩)
  · apply unipotent_of_le (V := unipotentEnvelope A V)
      (fun x hx => ((ClosedSubgroup.mem_inter_iff _ _ x).mp hx).1)
    exact (unipotentEnvelope_connected_unipotent A V hV).2

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
