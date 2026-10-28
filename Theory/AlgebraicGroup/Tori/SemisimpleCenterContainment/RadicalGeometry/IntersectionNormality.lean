module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.Basic
public import Theory.AlgebraicGroup.Unipotent.Normalizer

/-!
Algebraic endpoints of the normality argument in Borel, Chapter IV, 13.16.

The torus already normalizes `I(T)_u`. For each singular fixed subgroup, the
source bounds the dimension of the connected unipotent envelope by
`dim I(T)_u + 1`; the unipotent normalizer theorem then supplies normalization.
The solvable ambient case is proved directly from maximality of Borels.

The general geometric dimension bound and generation by torus-containing
Borels remain to be proved; the conditional endpoint here is not the general
normality theorem.
-/

universe u

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The torus normalizes the radical by its containment in `I(T)`. -/
public theorem torus_le_intersection_radical_normalizer
    {G : Variety k} [AlgebraicGroup G] (T U : ClosedSubgroup G)
    (hT : IsSubtorus T) (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U) :
    T ≤ U.normalizer := by
  have hTI := torus_le_torusBorelIntersection T hT
  intro t ht
  change t ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hU.2.2.1 t (hTI ht) x
  · intro hx
    have hback := hU.2.2.1 t⁻¹ (hTI (T.toSubgroup.inv_mem ht))
      (t * x * t⁻¹) hx
    have hcancel : t⁻¹ * (t * x * t⁻¹) * (t⁻¹)⁻¹ = x := by group
    rw [hcancel] at hback
    exact hback

/-- The dimension bound in 13.16 implies that its auxiliary unipotent group
normalizes `I(T)_u`. All containments and unipotence are discharged here. -/
public theorem unipotentEnvelope_le_radical_normalizer_of_dimension
    {G : Variety k} [AlgebraicGroup G] (T U A B V : ClosedSubgroup G)
    (hT : IsSubtorus T) (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (hTA : T ≤ A) (hAB : A ≤ B) (hB : IsBorelSubgroup B)
    (hV : IsUnipotentRadicalOf B V)
    (hdim : Variety.dimension (unipotentEnvelope A V).carrierVariety ≤
      Variety.dimension U.carrierVariety + 1) :
    unipotentEnvelope A V ≤ U.normalizer := by
  obtain ⟨hHc, hHu⟩ := unipotentEnvelope_connected_unipotent A V hV.2.1
  exact hHu.le_normalizer_of_le_of_dimension_le_add_one _ _ hHc
    (intersection_radical_le_unipotentEnvelope T U A B V hT hU hTA hAB hB hV)
    hdim

/-- A connected solvable ambient group is its only Borel, so every Borel
intersection has full identity component. -/
public theorem torusBorelIntersection_eq_top_of_solvable
    {G : Variety k} [AlgebraicGroup G] (hGc : Variety.IsConnected G)
    (hGs : Group.IsSolvable (Variety.Point G)) (T : ClosedSubgroup G) :
    torusBorelIntersection T = ClosedSubgroup.top := by
  have htopc : _root_.IsConnected
      ((ClosedSubgroup.top : ClosedSubgroup G) : Set (Variety.Point G)) := hGc
  have htops : Group.IsSolvable
      (Variety.Point (ClosedSubgroup.top : ClosedSubgroup G).carrierVariety) := by
    let : Group.IsSolvable (Variety.Point G) := hGs
    exact Group.isSolvable_of_isSolvable_injective
      (ClosedSubgroup.top : ClosedSubgroup G).inclusion_injective
  have htopI : (ClosedSubgroup.top : ClosedSubgroup G) ≤ torusBorelIntersection T := by
    rw [torusBorelIntersection_eq_identityComponentAmbient]
    apply connected_closedSubgroup_le_identityComponentAmbient _ _ htopc
    apply le_borelIntersection_of_forall
    intro B hB _
    rw [← hB.maximal ClosedSubgroup.top htopc htops (fun _ _ => trivial)]
    exact fun _ hx => hx
  exact SetLike.coe_injective (Set.Subset.antisymm (fun _ _ => trivial) htopI)

/-- The solvable ambient branch of the normality step of 13.16. -/
public theorem intersection_radical_normal_of_solvable
    {G : Variety k} [AlgebraicGroup G] (hGc : Variety.IsConnected G)
    (hGs : Group.IsSolvable (Variety.Point G)) (T U : ClosedSubgroup G)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U) : U.toSubgroup.Normal := by
  have hItop := torusBorelIntersection_eq_top_of_solvable hGc hGs T
  constructor
  intro x hx g
  exact hU.2.2.1 g (by rw [hItop]; trivial) x hx

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
