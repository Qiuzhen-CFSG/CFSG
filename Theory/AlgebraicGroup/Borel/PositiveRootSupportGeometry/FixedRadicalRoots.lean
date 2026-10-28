module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups.Connected
public import Theory.AlgebraicGroup.Borel.PositiveRootSupportGeometry.FixedRadicalRoots.Weights

/-!
Local reductions for torus fixed subgroups in Borel unipotent radicals.

Restriction to any closed subgroup preserves the unipotent radical of a
Borel. This identifies the intrinsic radical of the Borel restricted to a
subtorus centralizer with the literal ambient fixed subgroup. The latter is
connected and invariant under the containing maximal torus. A toral
centralizer has trivial intersection with the unipotent radical; the Cartan
and semiregular reductions below supply the two intended applications.

Sources: Borel, *Linear Algebraic Groups*, IV, 13.14, 13.17 and 13.18(4--5);
GLS3, Theorem 1.9.5(b,i). The Cartan/reductivity/semiregularity hypotheses
remain explicit in the relevant reductions. The singular rank-one radical
and weight-uniqueness argument is not asserted here: it must identify the
actual subgroup with the specified realization's root subgroup before these
local results discharge the inputs of `PositiveRootSupportGeometry`.
-/

universe u
namespace Theory.AlgebraicGroup.BorelFixedRadicalRoots
open SemisimpleCenterContainment
open SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

omit [IsAlgClosed k] in
/-- A unipotent radical is normalized by its defining overgroup. -/
public theorem radical_normalizer {B U : ClosedSubgroup G}
    (hU : IsUnipotentRadicalOf B U) : B ≤ U.normalizer := by
  intro b hb
  change b ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  change x ∈ U ↔ b * x * b⁻¹ ∈ U
  constructor
  · exact hU.2.2.1 b hb x
  · intro hx
    have h := hU.2.2.1 b⁻¹ (B.toSubgroup.inv_mem hb) (b * x * b⁻¹) hx
    simpa [mul_assoc] using h

/-- The literal fixed radical is connected for every subtorus of the Borel. -/
public theorem radical_fixed_connected {B U Q : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U)
    (hQ : IsSubtorus Q) (hQB : Q ≤ B) :
    _root_.IsConnected (U.pointwiseCentralizer Q : Set (Variety.Point G)) := by
  obtain ⟨V, hV, hVc⟩ :=
    exists_unipotentRadical_of_connected_solvable B hB.connected hB.solvable
  have hUc : _root_.IsConnected (U : Set (Variety.Point G)) := by
    rwa [unipotent_radical_unique hV hU] at hVc
  exact externalTorusFixed_isConnected_set U Q hUc hU.2.1 hQ
    (fun _ hx => radical_normalizer hU (hQB hx))

/-- The fixed radical is the unipotent radical of the ambient fixed Borel.
Normality is relative to that fixed Borel. -/
public theorem fixed_isUnipotentRadicalOf {B U : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U)
    (Q : ClosedSubgroup G) :
    IsUnipotentRadicalOf (B.pointwiseCentralizer Q) (U.pointwiseCentralizer Q) := by
  refine ⟨fun _ hx => ⟨hU.1 hx.1, hx.2⟩,
    unipotent_of_le (fun _ hx => hx.1) hU.2.1, ?_, ?_⟩
  · intro b hb x hx
    exact ⟨hU.2.2.1 b hb.1 x hx.1,
      Q.centralizer.toSubgroup.mul_mem
        (Q.centralizer.toSubgroup.mul_mem hb.2 hx.2)
        (Q.centralizer.toSubgroup.inv_mem hb.2)⟩
  · intro V hV hVu _ x hx
    exact ⟨hU.contains_unipotent_closedSubgroup hB.connected hB.solvable
      (fun _ hy => (hV hy).1) hVu hx, (hV hx).2⟩

/-- The radical of a Borel restricts to its literal preimage in any closed
overgroup carrier. No normality in the original ambient group is required. -/
public theorem intrinsic_isUnipotentRadicalOf {B U : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U)
    (C : ClosedSubgroup G) :
    IsUnipotentRadicalOf (C.inclusion.closedSubgroupPreimage B)
      (C.inclusion.closedSubgroupPreimage U) := by
  let BU := C.inclusion.closedSubgroupPreimage U
  refine ⟨fun _ hx => hU.1 hx, ?_, ?_, ?_⟩
  · intro x
    have hxU : C.includePoint (BU.includePoint x) ∈ U := (BU.pointEquiv x).property
    have hxuni : IsUnipotentElement G (C.includePoint (BU.includePoint x)) :=
      (closedSubgroup_unipotentElement_iff U hxU).mpr
        (hU.2.1 (U.pointEquiv.symm ⟨_, hxU⟩))
    have hxC : IsUnipotentElement C.carrierVariety (BU.includePoint x) :=
      (closedSubgroup_unipotentElement_iff C
        (C.pointEquiv (BU.includePoint x)).property).mp hxuni
    exact (closedSubgroup_unipotentElement_iff BU (BU.pointEquiv x).property).mp hxC
  · intro b hb x hx
    change C.inclusion.onPoints (b * x * b⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact hU.2.2.1 _ hb _ hx
  · intro V hVB hVu _ x hx
    let : AlgebraicGroup V.carrierVariety := V.carrierAlgebraicGroup
    let f := C.inclusion.comp V.inclusion
    have hIB : f.imageClosedSubgroup ≤ B := by
      rintro y ⟨v, rfl⟩
      exact hVB (V.pointEquiv v).property
    have hIu : IsUnipotentAlgebraicGroup f.imageClosedSubgroup.carrierVariety := by
      intro y
      obtain ⟨v, hv⟩ := (f.imageClosedSubgroup.pointEquiv y).property
      apply (closedSubgroup_unipotentElement_iff f.imageClosedSubgroup
        (f.imageClosedSubgroup.pointEquiv y).property).mp
      rw [← hv]
      exact morphism_preserves_unipotentElement f v (hVu v)
    have hIU := hU.contains_unipotent_closedSubgroup hB.connected hB.solvable hIB hIu
    apply hIU
    exact ⟨V.pointEquiv.symm ⟨x, hx⟩, rfl⟩

/-- Mapping the intrinsic preimage radical back into the original group gives
exactly the fixed radical, with the actual inclusion maps. -/
public theorem intrinsic_fixed_image (U Q : ClosedSubgroup G) :
    letI : AlgebraicGroup (Q.centralizer.inclusion.closedSubgroupPreimage U).carrierVariety :=
      (Q.centralizer.inclusion.closedSubgroupPreimage U).carrierAlgebraicGroup
    (Q.centralizer.inclusion.comp
      (Q.centralizer.inclusion.closedSubgroupPreimage U).inclusion).imageClosedSubgroup =
        U.pointwiseCentralizer Q := by
  apply SetLike.coe_injective
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨((Q.centralizer.inclusion.closedSubgroupPreimage U).pointEquiv y).property,
      (Q.centralizer.pointEquiv
        ((Q.centralizer.inclusion.closedSubgroupPreimage U).includePoint y)).property⟩
  · intro hx
    let xC := Q.centralizer.pointEquiv.symm ⟨x, hx.2⟩
    exact ⟨(Q.centralizer.inclusion.closedSubgroupPreimage U).pointEquiv.symm
      ⟨xC, hx.1⟩, rfl⟩

/-- An intrinsic radical supplied by a rank-one centralizer calculation has
ambient image equal to the original Borel radical fixed by the subtorus.
This is the transport needed when applying Borel 13.14 inside the centralizer. -/
public theorem fixed_radical_eq_intrinsic_radical_image {B U : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U)
    (Q : ClosedSubgroup G) (V : ClosedSubgroup Q.centralizer.carrierVariety)
    (hV : IsUnipotentRadicalOf (Q.centralizer.inclusion.closedSubgroupPreimage B) V) :
    letI : AlgebraicGroup V.carrierVariety := V.carrierAlgebraicGroup
    (Q.centralizer.inclusion.comp V.inclusion).imageClosedSubgroup =
      U.pointwiseCentralizer Q := by
  have heq := unipotent_radical_unique hV
    (intrinsic_isUnipotentRadicalOf hB hU Q.centralizer)
  subst V
  exact intrinsic_fixed_image U Q

/-- A toral centralizer has no nonidentity unipotent points. -/
public theorem fixed_eq_bot_of_toral_centralizer {U Q : ClosedSubgroup G}
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hQ : IsSubtorus Q.centralizer) :
    (U.pointwiseCentralizer Q).toSubgroup = ⊥ := by
  change U.toSubgroup ⊓ Q.centralizer.toSubgroup = ⊥
  rw [inf_comm]
  exact subtorus_inf_unipotent_eq_bot Q.centralizer U hQ hU

/-- The solvable reductive centralizer case reduces to disjointness of tori
and unipotent subgroups. -/
public theorem fixed_eq_bot_of_solvable_reductive_centralizer {U Q : ClosedSubgroup G}
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hred : IsReductiveAlgebraicGroup Q.centralizer.carrierVariety)
    (hsolv : Group.IsSolvable (Variety.Point Q.centralizer.carrierVariety)) :
    (U.pointwiseCentralizer Q).toSubgroup = ⊥ := by
  exact fixed_eq_bot_of_toral_centralizer hU
    (isTorus_of_isSolvable_of_isReductive hred hsolv)

/-- The Cartan and toral-radical inputs imply trivial full-torus fixed points.
Their independent geometric producers must discharge all three hypotheses. -/
public theorem radical_torus_fixed_eq_bot_of_cartan_geometry {B U T : ClosedSubgroup G}
    (hU : IsUnipotentRadicalOf B U)
    (hc : Variety.IsConnected T.centralizer.carrierVariety)
    (hs : Group.IsSolvable (Variety.Point T.centralizer.carrierVariety))
    (hr : ∀ R : ClosedSubgroup T.centralizer.carrierVariety,
      IsRadicalSubgroup R → IsSubtorus R) :
    (U.pointwiseCentralizer T).toSubgroup = ⊥ :=
  fixed_eq_bot_of_solvable_reductive_centralizer hU.2.1 ⟨hc, hr⟩ hs


omit [IsAlgClosed k] in
/-- The containing maximal torus preserves each subtorus fixed radical. -/
public theorem radical_fixed_invariant {B U T Q : ClosedSubgroup G}
    (hU : IsUnipotentRadicalOf B U) (hT : IsMaximalTorus T)
    (hTB : T ≤ B) (hQT : Q ≤ T) :
    IsClosedSubgroupInvariant T (U.pointwiseCentralizer Q) := by
  intro t ht x hx
  have htC : t ∈ Q.centralizer := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro q hq
    exact Subgroup.mem_centralizer_iff.mp (maximalTorus_le_centralizer hT ht)
      q (hQT hq)
  refine ⟨?_, ?_⟩
  · change t⁻¹ * x * t ∈ U
    simpa only [inv_inv] using hU.2.2.1 t⁻¹ (hTB (T.toSubgroup.inv_mem ht)) x hx.1
  · exact Q.centralizer.toSubgroup.mul_mem
      (Q.centralizer.toSubgroup.mul_mem (Q.centralizer.toSubgroup.inv_mem htC) hx.2) htC

/-- The semiregular containment from Borel 13.1 gives a solvable centralizer.
Together with reductivity from 13.17, this kills the fixed unipotent subgroup. -/
public theorem fixed_eq_bot_of_semiregular_geometry {U T Q : ClosedSubgroup G}
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) (hT : IsSubtorus T)
    (hred : IsReductiveAlgebraicGroup Q.centralizer.carrierVariety)
    (hsemi : Q.centralizer ≤ torusBorelIntersection T) :
    (U.pointwiseCentralizer Q).toSubgroup = ⊥ := by
  apply fixed_eq_bot_of_solvable_reductive_centralizer hU hred
  let f := Q.centralizer.inclusion.codRestrictClosedSubgroup (torusBorelIntersection T)
    (fun x => hsemi (Q.centralizer.pointEquiv x).property)
  have hf : Function.Injective f.onPoints := by
    intro x y hxy
    apply Q.centralizer.inclusion_injective
    exact congrArg (torusBorelIntersection T).inclusion.onPoints hxy
  let : Group.IsSolvable (Variety.Point (torusBorelIntersection T).carrierVariety) :=
    (SemisimpleCenterContainment.RadicalGeometry.torusBorelIntersection_connected_solvable
      T hT).2
  exact Group.isSolvable_of_isSolvable_injective hf

end Theory.AlgebraicGroup.BorelFixedRadicalRoots
