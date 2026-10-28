module

public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteIndex
public import Theory.AlgebraicGroup.Solvable.Nilpotent

/-!
# Transporters of regular semisimple elements

Borel, *Linear Algebraic Groups*, Chapter IV, §11.10: if a connected
nilpotent subgroup is the identity component of the centralizer of a
semisimple element, every conjugation carrying that element into the subgroup
normalizes it. Semisimple elements of the nilpotent subgroup are central
(§10.6(3)); inclusion and equality of dimensions identify the two connected
centralizers. No connectedness of the full torus centralizer is used.
-/

namespace Theory.AlgebraicGroup.BorelElementCoverage

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

omit [IsAlgClosed k] in
private theorem carrier_connected (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

omit [IsAlgClosed k] in
private theorem conjugate_connected {H : ClosedSubgroup G}
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) (g : Variety.Point G) :
    _root_.IsConnected (H.conjugate g : Set (Variety.Point G)) := by
  have heq : (H.conjugate g : Set (Variety.Point G)) =
      (AlgebraicGroup.conjugationByMorphism G g).toFun ''
        (H : Set (Variety.Point G)) := by
    ext x
    constructor
    · intro hx
      refine ⟨g⁻¹ * x * g, (H.mem_conjugate_iff g x).mp hx, ?_⟩
      rw [AlgebraicGroup.conjugationByMorphism_apply]
      simp [mul_assoc]
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, H.mem_conjugate_iff,
        AlgebraicGroup.conjugationByMorphism_apply]
      change y ∈ H.toSubgroup at hy
      simpa [mul_assoc] using hy
  rw [heq]
  exact hH.image _ (AlgebraicGroup.conjugationByMorphism G g).continuous.continuousOn

private theorem conjugate_identityComponent_le (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    H.identityComponentAmbient.conjugate g ≤ (H.conjugate g).identityComponentAmbient := by
  apply connected_closedSubgroup_le_identityComponentAmbient
  · exact conjugate_connected H.identityComponentAmbient_isConnected g
  · intro x hx
    exact ((H.mem_conjugate_iff g x).mpr
      (H.identityComponentAmbient_le
        ((H.identityComponentAmbient.mem_conjugate_iff g x).mp hx)))

/-- Taking the ambient identity component commutes with conjugation. -/
public theorem conjugate_identityComponentAmbient (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    H.identityComponentAmbient.conjugate g = (H.conjugate g).identityComponentAmbient := by
  apply SetLike.coe_injective
  apply Set.Subset.antisymm (conjugate_identityComponent_le H g)
  have hback := conjugate_identityComponent_le (H.conjugate g) g⁻¹
  rw [ClosedSubgroup.conjugate_conjugate, inv_mul_cancel,
    ClosedSubgroup.conjugate_one] at hback
  intro x hx
  apply (H.identityComponentAmbient.mem_conjugate_iff g x).mpr
  apply hback
  apply ((H.conjugate g).identityComponentAmbient.mem_conjugate_iff g⁻¹ _).mpr
  change x ∈ (H.conjugate g).identityComponentAmbient.toSubgroup at hx
  simpa [mul_assoc] using hx

omit [IsAlgClosed k] in
/-- Conjugation transports the actual centralizer of a single point. -/
public theorem pointCentralizer_conjugate (t g : Variety.Point G) :
    semisimpleCommutatorPointCentralizer (g * t * g⁻¹) =
      (semisimpleCommutatorPointCentralizer t).conjugate g := by
  apply SetLike.coe_injective
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, ClosedSubgroup.mem_conjugate_iff]
  change x ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set (Variety.Point G)) ↔
    g⁻¹ * x * g ∈ Subgroup.centralizer ({t} : Set (Variety.Point G))
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro hx
    have h := congrArg (fun z : Variety.Point G => g⁻¹ * z * g) hx
    simpa [mul_assoc] using h
  · intro hx
    have h := congrArg (fun z : Variety.Point G => g * z * g⁻¹) hx
    simpa [mul_assoc] using h

/-- In a connected nilpotent closed subgroup, ambient semisimple elements
centralize the whole subgroup. -/
public theorem le_pointCentralizer_of_mem_semisimple_nilpotent
    (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G)))
    (hnil : Group.IsNilpotent (Variety.Point H.carrierVariety))
    {s : Variety.Point G} (hs : s ∈ H.toSubgroup) (hss : IsSemisimpleElement G s) :
    H ≤ semisimpleCommutatorPointCentralizer s := by
  let : Group.IsNilpotent (Variety.Point H.carrierVariety) := hnil
  let sH : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨s, hs⟩
  have hsH : IsSemisimpleElement H.carrierVariety sH :=
    (closedSubgroup_semisimpleElement_iff H hs).mp hss
  have hcentral := semisimpleElement_mem_center_of_isNilpotent_of_solvable_connected
    (G := H.carrierVariety) inferInstance (carrier_connected H hH) hnil hsH
  intro x hx
  let xH : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨x, hx⟩
  have heq := congrArg H.inclusion.onPoints (Subgroup.mem_center_iff.mp hcentral xH)
  change x ∈ Subgroup.centralizer ({s} : Set (Variety.Point G))
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  exact (show x * s = s * x from heq).symm

/-- The transporter step in §11.10, stated for any nilpotent connected
centralizer component. The convention here is the literal left-coset test
`g⁻¹ * t * g ∈ H`. -/
public theorem transporter_mem_normalizer_of_regular_semisimple
    (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G)))
    (hnil : Group.IsNilpotent (Variety.Point H.carrierVariety))
    (t : Variety.Point G) (ht : IsSemisimpleElement G t)
    (hregular : (semisimpleCommutatorPointCentralizer t).identityComponentAmbient = H)
    (g : Variety.Point G) (hg : g⁻¹ * t * g ∈ H.toSubgroup) :
    g ∈ H.normalizer.toSubgroup := by
  let c : AlgebraicGroup.Morphism G G :=
    { toVariety := AlgebraicGroup.conjugationByMorphism G g⁻¹
      map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
      map_mul := by
        intro x y
        simp [AlgebraicGroup.conjugationByMorphism_apply, mul_assoc] }
  have hs : IsSemisimpleElement G (g⁻¹ * t * g) := by
    have h := morphism_preserves_semisimpleElement c t ht
    change IsSemisimpleElement G (g⁻¹ * t * (g⁻¹)⁻¹) at h
    simpa only [inv_inv] using h
  have hle := le_pointCentralizer_of_mem_semisimple_nilpotent H hH hnil hg hs
  have hc : semisimpleCommutatorPointCentralizer (g⁻¹ * t * g) =
      (semisimpleCommutatorPointCentralizer t).conjugate g⁻¹ := by
    simpa only [inv_inv] using pointCentralizer_conjugate t g⁻¹
  have heq : (semisimpleCommutatorPointCentralizer (g⁻¹ * t * g)).identityComponentAmbient = H := by
    rw [← hregular]
    apply ClosedSubgroup.identityComponentAmbient_eq_of_le_of_dimension_le
    · simpa only [hregular] using hle
    · rw [hc]
      exact (ClosedSubgroup.conjugate_dimension_eq _ _).symm.le
  have hconj : H.conjugate g⁻¹ = H := by
    rw [← hregular, conjugate_identityComponentAmbient]
    rw [← hc, heq, hregular]
  change g ∈ Subgroup.normalizer (H.toSubgroup : Set (Variety.Point G))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hx : x ∈ H.conjugate g⁻¹ ↔ x ∈ H.toSubgroup := by rw [hconj]; rfl
  simpa only [ClosedSubgroup.mem_conjugate_iff, inv_inv] using hx.symm

/-- A closed subgroup containing the ambient identity component of another
closed subgroup has finite relative index there. No ambient finite-index
hypothesis is needed. -/
public theorem finiteIndex_subgroupOf_of_identityComponentAmbient_le
    (H N : ClosedSubgroup G) (hNH : N.identityComponentAmbient ≤ H) :
    (H.toSubgroup.subgroupOf N.toSubgroup).FiniteIndex := by
  let e : Variety.Point N.carrierVariety ≃* N.toSubgroup := Equiv.mulEquiv N.pointEquiv
  let I := AlgebraicGroup.identityComponentSubgroup N.carrierVariety
  let J : Subgroup N.toSubgroup := I.map e.toMonoidHom
  let : J.FiniteIndex := by
    constructor
    change (I.map e.toMonoidHom).index ≠ 0
    rw [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective I]
    exact Subgroup.FiniteIndex.index_ne_zero
  apply Subgroup.finiteIndex_of_le (H := J)
  rintro x ⟨y, hy, rfl⟩
  apply hNH
  apply (N.mem_identityComponentAmbient_iff _).mpr
  exact ⟨y, hy, rfl⟩

end Theory.AlgebraicGroup.BorelElementCoverage
