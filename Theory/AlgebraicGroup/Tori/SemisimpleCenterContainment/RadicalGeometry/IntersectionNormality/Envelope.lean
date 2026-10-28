module
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.TorusRigidity.FiniteBorels
public import Theory.AlgebraicGroup.Borel.PositiveRootSupportGeometry.FixedRadicalRoots

/-!
# The actual unipotent envelope in Bor1 13.16

For a Borel `B`, its supplied unipotent radical `V`, and a subtorus `S`
of a maximal torus `T≤B`, this module uses precisely
`H=(I(B^S)∩V)^0`. It proves that `H` is connected and unipotent,
`T` normalizes it, `I(T)_u≤H`, and `H^S=V^S`. Unipotent fixed points
of every subtorus with solvable centralizer already lie in `I(T)_u`.

The normalizer consumer applies the proved external-torus dimension formula
and unipotent normalizer theorem to the two remaining local bounds of
Bor1 IV, 13.15. No normality of `I(T)_u` is assumed, and no quotient by it
is formed before normality has been proved. The rank-one geometry producing
those bounds, and torus-Borel generation in 13.7, remain independent sources.
-/

public section
namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- The connected solvable centralizer lies in the actual Borel intersection. -/
theorem solvable_centralizer_le_intersection (hG : Variety.IsConnected G)
    {S T : ClosedSubgroup G} (hS : IsSubtorus S) (hST : S ≤ T)
    (hs : Group.IsSolvable (Variety.Point S.centralizer.carrierVariety)) :
    S.centralizer ≤ torusBorelIntersection T := by
  rw [torusBorelIntersection_eq_identityComponentAmbient]
  apply connected_closedSubgroup_le_identityComponentAmbient
  · let : ConnectedSpace (Variety.Point S.centralizer.carrierVariety) :=
      connectedSpace_iff_univ.mpr (CartanGeometry.subtorus_centralizer_isConnected hG hS)
    change _root_.IsConnected (S.centralizer.toSubgroup : Set (Variety.Point G))
    rw [← S.centralizer.range_inclusion]
    exact isConnected_range S.centralizer.inclusion.toVariety.continuous
  · apply le_borelIntersection_of_forall
    intro B hB hTB
    exact BorelRestriction.centralizer_le_borel_of_solvable hG hS hB
      (fun _ hx => hTB (hST hx)) hs

/-- Fixed points in the solvable-centralizer branch belong to `I(T)_u`. -/
theorem unipotent_fixed_le_intersection_radical_of_solvable
    (hG : Variety.IsConnected G) {S T U V : ClosedSubgroup G}
    (hS : IsSubtorus S) (hT : IsSubtorus T) (hST : S ≤ T)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (hV : IsUnipotentAlgebraicGroup V.carrierVariety)
    (hs : Group.IsSolvable (Variety.Point S.centralizer.carrierVariety)) :
    V.pointwiseCentralizer S ≤ U := by
  obtain ⟨hIc,hIs⟩ := torusBorelIntersection_connected_solvable T hT
  exact hU.contains_unipotent_closedSubgroup hIc hIs
    (fun _ hx => solvable_centralizer_le_intersection hG hS hST hs hx.2)
    (unipotent_of_le (fun _ hx => hx.1) hV)

/-- The source envelope contains the fixed radical of the original Borel. -/
theorem borel_fixed_radical_le_envelope {B V S : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hV : IsUnipotentRadicalOf B V)
    (hS : IsSubtorus S) (hSB : S ≤ B) :
    V.pointwiseCentralizer S ≤ unipotentEnvelope (B.pointwiseCentralizer S) V := by
  apply connected_le_unipotentEnvelope
  · exact BorelFixedRadicalRoots.radical_fixed_connected hB hV hS hSB
  · exact fun _ hx => ⟨hV.1 hx.1,hx.2⟩
  · exact fun _ hx => hx.1

/-- `H^S=B_u^S` for the literal `H=(I(B^S)∩B_u)^0`. -/
theorem unipotentEnvelope_fixed_eq {B V S : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hV : IsUnipotentRadicalOf B V)
    (hS : IsSubtorus S) (hSB : S ≤ B) :
    (unipotentEnvelope (B.pointwiseCentralizer S) V).pointwiseCentralizer S =
      V.pointwiseCentralizer S := by
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨(((torusBorelIntersection (B.pointwiseCentralizer S)).inter V).identityComponentAmbient_le hx.1).2,hx.2⟩
  · intro x hx
    exact ⟨borel_fixed_radical_le_envelope hB hV hS hSB hx,hx.2⟩

private theorem normalizer_identityComponent {X : ClosedSubgroup G} {g : Variety.Point G}
    (hg : g ∈ X.normalizer.toSubgroup) :
    g ∈ X.identityComponentAmbient.normalizer.toSubgroup := by
  have heq : X.identityComponentAmbient.conjugate g = X.identityComponentAmbient := by
    rw [BorelElementCoverage.conjugate_identityComponentAmbient,
      ClosedSubgroup.conjugate_eq_self_of_mem_normalizer g hg]
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  have h := X.identityComponentAmbient.mem_conjugate_iff g (g*x*g⁻¹)
  rw [heq] at h
  change (g*x*g⁻¹ ∈ X.identityComponentAmbient.toSubgroup) ↔
    (g⁻¹*(g*x*g⁻¹)*g ∈ X.identityComponentAmbient.toSubgroup) at h
  change x ∈ X.identityComponentAmbient.toSubgroup ↔ g*x*g⁻¹ ∈ X.identityComponentAmbient.toSubgroup
  simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using h.symm

/-- The containing torus normalizes the actual source envelope. -/
theorem torus_le_unipotentEnvelope_normalizer {B V S T : ClosedSubgroup G}
    (hV : IsUnipotentRadicalOf B V) (hT : IsMaximalTorus T)
    (hTB : T ≤ B) (hST : S ≤ T) :
    T ≤ (unipotentEnvelope (B.pointwiseCentralizer S) V).normalizer := by
  have hTA : T ≤ B.pointwiseCentralizer S := by
    intro t ht
    refine ⟨hTB ht, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp (maximalTorus_le_centralizer hT ht) s (hST hs)
  have hTI : T ≤ torusBorelIntersection (B.pointwiseCentralizer S) :=
    fun _ ht => torusBorelIntersection_mono hTA (torus_le_torusBorelIntersection T hT.1 ht)
  intro t ht
  apply normalizer_identityComponent
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  exact and_congr
    (Subgroup.mem_normalizer_iff.mp
      ((torusBorelIntersection (B.pointwiseCentralizer S)).toSubgroup.le_normalizer (hTI ht)) x)
    (Subgroup.mem_normalizer_iff.mp (BorelFixedRadicalRoots.radical_normalizer hV (hTB ht)) x)

/-- The envelope is the literal connected unipotent group needed in 13.16,
with its full-torus fixed points already contained in the intersection radical. -/
theorem unipotentEnvelope_source_geometry
    (hG : Variety.IsConnected G) {B V S T U : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hV : IsUnipotentRadicalOf B V)
    (hT : IsMaximalTorus T) (hTB : T ≤ B) (hS : IsSubtorus S) (hST : S ≤ T)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U) :
    let H := unipotentEnvelope (B.pointwiseCentralizer S) V
    _root_.IsConnected (H : Set (Variety.Point G)) ∧
    IsUnipotentAlgebraicGroup H.carrierVariety ∧ T ≤ H.normalizer ∧ U ≤ H ∧
    H.pointwiseCentralizer S = V.pointwiseCentralizer S ∧
    H.pointwiseCentralizer T ≤ U := by
  let H := unipotentEnvelope (B.pointwiseCentralizer S) V
  have hTA : T ≤ B.pointwiseCentralizer S := by
    intro t ht
    refine ⟨hTB ht, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp (maximalTorus_le_centralizer hT ht) s (hST hs)
  have hgeom := unipotentEnvelope_connected_unipotent (B.pointwiseCentralizer S) V hV.2.1
  refine ⟨hgeom.1,hgeom.2,torus_le_unipotentEnvelope_normalizer hV hT hTB hST,
    intersection_radical_le_unipotentEnvelope T U (B.pointwiseCentralizer S) B V
      hT.1 hU hTA (fun _ hx => hx.1) hB hV,
    unipotentEnvelope_fixed_eq hB hV hS (fun _ hx => hTB (hST hx)), ?_⟩
  exact unipotent_fixed_le_intersection_radical_of_solvable hG hT.1 hT.1
    (fun _ hx => hx) hU hgeom.2
    (CartanGeometry.maximalTorus_centralizer_connected_solvable hG hT).2


/-- The two literal fixed-subgroup bounds of 13.15 imply normalization.
The envelope, its connectedness, torus action, and fixed-subgroup identities
are constructed from the original Borel and its actual unipotent radical. -/
theorem borel_fixed_radical_normalizes_of_rankOne_bounds
    (hG : Variety.IsConnected G) {B V T U : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hV : IsUnipotentRadicalOf B V)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (S : CodimensionOneSubtorus T)
    (hdim : Variety.dimension (V.pointwiseCentralizer S.1).carrierVariety ≤
      Variety.dimension ((V.pointwiseCentralizer S.1).inter U).carrierVariety + 1)
    (hother : ∀ Q : CodimensionOneSubtorus T, Q.1 ≠ S.1 →
      ¬ Group.IsSolvable (Variety.Point Q.1.centralizer.carrierVariety) →
      (torusBorelIntersection (B.pointwiseCentralizer S.1)).pointwiseCentralizer Q.1 ≤
        torusBorelIntersection T) :
    V.pointwiseCentralizer S.1 ≤ U.normalizer := by
  let H := unipotentEnvelope (B.pointwiseCentralizer S.1) V
  obtain ⟨hHc,hHu,hTH,hUH,hHS,hHT⟩ :=
    unipotentEnvelope_source_geometry hG hB hV hT hTB S.2.1 S.2.2.1 hU
  have hdimH : Variety.dimension H.carrierVariety ≤ Variety.dimension U.carrierVariety + 1 := by
    apply externalTorusFixed_dimension_le H U T S.1 hT.1 hTH hHT
    · intro Q hQS
      by_cases hsolv : Group.IsSolvable (Variety.Point Q.1.centralizer.carrierVariety)
      · exact unipotent_fixed_le_intersection_radical_of_solvable hG Q.2.1 hT.1
          Q.2.2.1 hU hHu hsolv
      · exact unipotentEnvelope_fixed_le_radical T U (B.pointwiseCentralizer S.1) V Q.1
          hT.1 hU hV.2.1 (hother Q hQS hsolv)
    · rw [hHS]
      exact hdim
  have hHN := hHu.le_normalizer_of_le_of_dimension_le_add_one H U hHc hUH hdimH
  exact fun _ hx => hHN (borel_fixed_radical_le_envelope hB hV S.2.1
    (fun _ hs => hTB (S.2.2.1 hs)) hx)

/-- The actual centralizer radical maps into `I(T)`; Borel restriction and
radical containment in each restricted Borel discharge the source premise. -/
theorem centralizer_radical_image_le_intersection
    (hG : Variety.IsConnected G) {S T : ClosedSubgroup G}
    (hS : IsSubtorus S) (hST : S ≤ T)
    (R : ClosedSubgroup S.centralizer.carrierVariety) (hR : IsRadicalSubgroup R) :
    letI : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
    (S.centralizer.inclusion.comp R.inclusion).imageClosedSubgroup ≤ torusBorelIntersection T := by
  let _ : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
  let f := S.centralizer.inclusion.comp R.inclusion
  rw [torusBorelIntersection_eq_identityComponentAmbient]
  apply connected_closedSubgroup_le_identityComponentAmbient
  · apply f.imageClosedSubgroup_isConnected
    let : ConnectedSpace {x : Variety.Point S.centralizer.carrierVariety // x ∈ (R : Set _)} :=
      Subtype.connectedSpace hR.connected
    let : ConnectedSpace (Variety.Point R.carrierVariety) :=
      (Variety.closedSubvarietyPointHomeomorph R.isZariskiClosed).connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  · apply le_borelIntersection_of_forall
    intro B hB hTB
    have hRB := normal_connected_solvable_le_borel R
      (S.centralizer.inclusion.closedSubgroupPreimage B) hR.normal hR.connected hR.solvable
      (BorelRestriction.isBorel_centralizer_restriction hG S B hS hB
        (fun _ hx => hTB (hST hx)))
    rintro x ⟨r,rfl⟩
    exact hRB (R.pointEquiv r).property

/-- The unipotent radical of a torus centralizer maps into the candidate
`I(T)_u`. Ambient normality of this image is neither asserted nor needed. -/
theorem centralizer_unipotent_radical_image_le
    (hG : Variety.IsConnected G) {S T U : ClosedSubgroup G}
    (hS : IsSubtorus S) (hT : IsSubtorus T) (hST : S ≤ T)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (R V : ClosedSubgroup S.centralizer.carrierVariety)
    (hR : IsRadicalSubgroup R) (hV : IsUnipotentRadicalOf R V) :
    letI : AlgebraicGroup V.carrierVariety := V.carrierAlgebraicGroup
    (S.centralizer.inclusion.comp V.inclusion).imageClosedSubgroup ≤ U := by
  let _ : AlgebraicGroup V.carrierVariety := V.carrierAlgebraicGroup
  let _ : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
  let f := S.centralizer.inclusion.comp V.inclusion
  obtain ⟨hIc,hIs⟩ := torusBorelIntersection_connected_solvable T hT
  apply hU.contains_unipotent_closedSubgroup hIc hIs
  · rintro x ⟨v,rfl⟩
    apply centralizer_radical_image_le_intersection hG hS hST R hR
    exact ⟨R.pointEquiv.symm ⟨V.includePoint v,hV.1 (V.pointEquiv v).property⟩,rfl⟩
  · exact hV.2.1.of_surjective
      (f.codRestrictClosedSubgroup f.imageClosedSubgroup (fun x => ⟨x,rfl⟩))
      (f.codRestrictImageClosedSubgroup_surjective (fun x => ⟨x,rfl⟩))

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
