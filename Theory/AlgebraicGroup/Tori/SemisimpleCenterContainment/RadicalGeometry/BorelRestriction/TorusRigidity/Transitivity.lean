module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.TorusRigidity.Conjugation
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.TorusRigidity.SolvableConjugacy
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.CartanGeometry.Source
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.Basic

/-!
# Fixed-component centralizer transitivity and Borel restriction

The actual connected preimage of a torus-fixed component consists of products
of a centralizer point and a Borel point. To prove this, restrict conjugation
to the original Borel, use torus-family rigidity on a diagonal morphism whose
kernel is its unipotent radical, and apply pointwise solvable torus conjugacy.
The prescribed fixed component is therefore a single centralizer orbit.

Its complete homogeneous geometry proves that the restriction of the original
Borel to the torus centralizer is Borel. Connectedness of that centralizer is
supplied by the already proved source theorem, so the final conclusion has no
extra geometric, transitivity, or centralizer-connectedness assumption.

This is Borel, *Linear Algebraic Groups*, §11.15, with the literal universal
restriction interface consumed by the semisimple-center argument.
-/

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
open BorelGeometricConjugacy Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Variety k} [AlgebraicGroup H]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

omit [IsAlgClosed k] in
private theorem carrier_connected (B : ClosedSubgroup H) (hB : IsBorelSubgroup B) :
    Variety.IsConnected B.carrierVariety := by
  let : ConnectedSpace {x : Variety.Point H // x ∈ (B : Set (Variety.Point H))} :=
    Subtype.connectedSpace hB.connected
  let : ConnectedSpace (Variety.Point B.carrierVariety) :=
    (Variety.closedSubvarietyPointHomeomorph B.isZariskiClosed).connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

public theorem componentPreimage_centralizer_decomposition {B : ClosedSubgroup H}
    (M : CompleteModel B) (hH : Variety.IsConnected H) (hB : IsBorelSubgroup B)
    (S : ClosedSubgroup H) (hS : IsSubtorus S) (hSB : S ≤ B)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
    (x : Point (fixedComponent M S Z).toGeometric)
    (hx : (fixedComponent M S Z).inclusion x = modelBasePoint M)
    (y : Point (componentPreimage M (fixedComponent M S Z)).toGeometric) :
    ∃ (c : Variety.Point S.centralizer.carrierVariety) (b : Variety.Point B.carrierVariety),
      affinePointEquiv H ((componentPreimage M (fixedComponent M S Z)).inclusion y) =
        S.centralizer.inclusion.onPoints c * B.inclusion.onPoints b := by
  let i := S.inclusion.codRestrictClosedSubgroup B (fun t => hSB (S.pointEquiv t).property)
  obtain ⟨A, hA, hiA⟩ := exists_maximalTorus_containing i.imageClosedSubgroup (morphism_image_isTorus i hS)
  have hBc := carrier_connected B hB
  obtain ⟨U, hU, _, _, hAU⟩ :=
    exists_unipotentRadical_complement_of_maximalTorus_solvable_connected hB.solvable hBc A hA
  obtain ⟨n, q, hq⟩ := exists_torus_morphism_kernel_unipotentRadical hBc hB.solvable U hU
  let j := torusFamilySlice (componentConjugationFamily M S Z)
    (componentConjugationFamily_one M S Z) (componentConjugationFamily_mul M S Z) y
  have hij (t : Variety.Point S.carrierVariety) : q.onPoints (i.onPoints t) = q.onPoints (j.onPoints t) := by
    rw [torusFamilySlice_apply]
    exact (componentPreimage_quotient_conjugation_constant M hH hB S hS hSB Z x hx q
      (dVariety_isTorus n) y t).symm
  obtain ⟨u, _, hu⟩ := torus_homomorphisms_conjugate_of_quotient_eq hBc hB.solvable U A hU hAU
    hS q hq i j hiA hij
  let g := affinePointEquiv H ((componentPreimage M (fixedComponent M S Z)).inclusion y)
  let b := B.inclusion.onPoints u
  let c := g * b⁻¹
  have hc : c ∈ S.centralizer.toSubgroup := by
    change c ∈ Subgroup.centralizer (S.toSubgroup : Set (Variety.Point H))
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    let t := S.pointEquiv.symm ⟨a, ha⟩
    have ht : S.inclusion.onPoints t = a := congrArg Subtype.val (S.pointEquiv.apply_symm_apply ⟨a, ha⟩)
    have he := congrArg B.inclusion.onPoints (hu t)
    change B.inclusion.onPoints ((torusFamilySlice _ _ _ y).onPoints t) =
      B.inclusion.onPoints (u⁻¹ * i.onPoints t * u) at he
    rw [torusFamilySlice_apply, componentConjugationFamily_apply, map_mul, map_mul, map_inv,
      AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply, ht] at he
    change g⁻¹ * a * g = b⁻¹ * a * b at he
    have he' := congrArg (fun z : Variety.Point H => g * z * b⁻¹) he
    change a * c = c * a
    dsimp [c]
    convert he' using 1 <;> group
  refine ⟨S.centralizer.pointEquiv.symm ⟨c, hc⟩, u, ?_⟩
  change g = (S.centralizer.pointEquiv (S.centralizer.pointEquiv.symm ⟨c, hc⟩)).val * b
  rw [S.centralizer.pointEquiv.apply_symm_apply]
  dsimp [c]
  group

public theorem fixedComponent_centralizer_transitive {B : ClosedSubgroup H}
    (M : CompleteModel B) (hH : Variety.IsConnected H) (hB : IsBorelSubgroup B)
    (S : ClosedSubgroup H) (hS : IsSubtorus S) (hSB : S ≤ B)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
    (x : Point (fixedComponent M S Z).toGeometric)
    (hx : (fixedComponent M S Z).inclusion x = modelBasePoint M)
    (y : Point (fixedComponent M S Z).toGeometric) :
    ∃ c : Variety.Point S.centralizer.carrierVariety,
      (fixedComponentCentralizerAction M S (CartanGeometry.subtorus_centralizer_isConnected hH hS) Z).toMulAction.smul c x = y := by
  obtain ⟨g, hg⟩ := modelBasePoint_transitive M ((fixedComponent M S Z).inclusion y)
  obtain ⟨p, hp⟩ := (point_mem_componentPreimage_iff M (fixedComponent M S Z)
    ((affinePointEquiv H).symm g)).mpr (by
      rw [Equiv.apply_symm_apply]
      exact ⟨y, hg.symm⟩)
  obtain ⟨c, b, hcb⟩ := componentPreimage_centralizer_decomposition M hH hB S hS hSB Z x hx p
  rw [hp, Equiv.apply_symm_apply] at hcb
  refine ⟨c, ?_⟩
  have hinj : Function.Injective (fun z : Point (fixedComponent M S Z).toGeometric => (fixedComponent M S Z).inclusion z) := by
    intro a b hab
    apply Subtype.ext
    apply (cancel_mono (fixedComponent M S Z).inclusion.hom).mp
    exact congrArg Subtype.val hab
  apply hinj
  rw [fixedComponentCentralizerAction_smul, hx, ← hg, hcb]
  have hb := (modelBasePoint_stabilizer M (B.inclusion.onPoints b)).mpr (B.pointEquiv b).property
  let := M.action.toMulAction
  change S.centralizer.inclusion.onPoints c • modelBasePoint M =
    (S.centralizer.inclusion.onPoints c * B.inclusion.onPoints b) • modelBasePoint M
  rw [mul_smul]
  exact congrArg (fun z : Point M.variety => S.centralizer.inclusion.onPoints c • z) hb.symm

public theorem isBorel_centralizer_restriction (hH : Variety.IsConnected H)
    (S B : ClosedSubgroup H) (hS : IsSubtorus S) (hB : IsBorelSubgroup B) (hSB : S ≤ B) :
    IsBorelSubgroup (S.centralizer.inclusion.closedSubgroupPreimage B) := by
  obtain ⟨M, Z, x, hx⟩ := exists_model_fixedComponent S B hB hSB
  exact isBorel_of_fixedComponent_transitive S B hS hB hSB M Z
    (fixedComponentCentralizerAction M S (CartanGeometry.subtorus_centralizer_isConnected hH hS) Z)
    x hx (fixedComponentCentralizerAction_smul M S _ Z)
    (fixedComponent_centralizer_transitive M hH hB S hS hSB Z x hx)

public theorem uniform_subtorus_borel_restriction :
    IntersectionNormality.UniformSubtorusBorelRestriction k := by
  intro G _ hG S hS _ B hB hSB
  exact isBorel_centralizer_restriction hG S B hS hB hSB
end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
