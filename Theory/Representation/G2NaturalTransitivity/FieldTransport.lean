module

public import Theory.Representation.G2.RestrictedModules.NaturalCoordinates
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport

/-!
# Field transport for the natural G₂ quotient and its derived action

A field isomorphism transports the six nonscalar coordinates semilinearly.
The quotient-coordinate equivalence identifies this with a semilinear map
between the actual trace-zero octonion quotients. Coefficient transport of the
octonion automorphism groups intertwines this map, including on the derived
subgroups. This permits binary orbit calculations to be used for every field
of order two, without identifying G₂(2) with G₂(2)′.

The natural module is the one in Aschbacher--Smith G.9.3(10), printed p.354.
Coordinate and group transport conventions are those of the attributed ATLAS
ports imported above; no additional ATLAS source is copied here.
-/

@[expose] public noncomputable section

namespace Atlas.G2.Natural
open Atlas.SplitOctonion
variable {F K : Type*} [Field F] [Field K] [CharP F 2] [CharP K 2]
namespace Transitivity
open Restricted.NaturalCoordinates
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Coefficient transport gives a semilinear equivalence of the actual quotients. -/
def fieldTransport (e : F ≃+* K) : LinearEquiv (e : F →+* K) (σ' := (e.symm : K →+* F))
    (Natural.Space F) (Natural.Space K) where
  toFun x := quotientClass K (fun i => e (coordinates F x i))
  invFun y := quotientClass F (fun i => e.symm (coordinates K y i))
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp only [map_add, Pi.add_apply]; exact map_add _ _ _
  map_smul' r x := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    exact map_smul (quotientClass K) (e r) (fun i => e (coordinates F x i))

/-- Field transport acts coefficientwise on the six nonscalar coordinates. -/
theorem coordinates_fieldTransport (e : F ≃+* K) (x : Natural.Space F) :
    coordinates K (fieldTransport e x) = fun i => e (coordinates F x i) :=
  coordinates_quotientClass K _

/-- The coordinate action commutes with transport to an isomorphic field. -/
theorem coordinate_action_fieldEquiv (e : F ≃+* K) (g : Model F) (v : Fin 6 → F) :
    Restricted.NaturalCoordinates.action K (fieldEquiv e g) (fun i => e (v i)) =
      fun i => e (Restricted.NaturalCoordinates.action F g v i) := by
  have hrep : mapCoefficients e (representative F v).val =
      (representative K (fun i => e (v i))).val := by
    ext i
    fin_cases i <;> simp [mapCoefficients, representative]
  have h := fieldEquiv_action e g (representative F v).val
  rw [hrep] at h
  ext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2
  · exact congrFun h 5
  · exact congrFun h 6
  · exact congrFun h 7

/-- The semilinear quotient equivalence intertwines the full octonion groups. -/
theorem fieldTransport_action (e : F ≃+* K) (g : Model F) (x : Natural.Space F) :
    fieldTransport e (Natural.action F g x) =
      Natural.action K (fieldEquiv e g) (fieldTransport e x) := by
  apply (equiv K).injective
  have hF := (repEquiv F).isIntertwining' g
  have hK := (repEquiv K).isIntertwining' (fieldEquiv e g)
  have hFx := LinearMap.congr_fun hF x
  have hKx := LinearMap.congr_fun hK (fieldTransport e x)
  change coordinates K (fieldTransport e (Natural.action F g x)) = _
  rw [coordinates_fieldTransport]
  change coordinates F (Natural.action F g x) =
    Restricted.NaturalCoordinates.action F g (coordinates F x) at hFx
  change coordinates K (Natural.action K (fieldEquiv e g) (fieldTransport e x)) =
    Restricted.NaturalCoordinates.action K (fieldEquiv e g)
      (coordinates K (fieldTransport e x)) at hKx
  change _ = coordinates K (Natural.action K (fieldEquiv e g) (fieldTransport e x))
  rw [hKx, coordinates_fieldTransport, coordinate_action_fieldEquiv, hFx]

/-- The actual group comparison restricts to an equivalence of derived subgroups. -/
def derivedFieldTransport (e : F ≃+* K) : commutator (Model F) ≃* commutator (Model K) :=
  ((fieldEquiv e).subgroupMap _).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _
      (fieldEquiv e).surjective]
    rfl))

/-- The quotient and derived-group comparisons intertwine the derived actions. -/
theorem fieldTransport_derivedAction (e : F ≃+* K) (g : commutator (Model F))
    (x : Natural.Space F) :
    fieldTransport e (derivedAction F g x) =
      derivedAction K (derivedFieldTransport e g) (fieldTransport e x) :=
  fieldTransport_action e g.val x

end Transitivity

end Atlas.G2.Natural
