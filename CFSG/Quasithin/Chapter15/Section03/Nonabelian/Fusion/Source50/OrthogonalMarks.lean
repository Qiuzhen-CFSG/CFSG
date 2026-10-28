module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.OriginalCoordinates
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry

/-!
# The original singular point and definite-plane marking

The earlier fusion calculation constructs the singular central involution
and the nonsingular fixed-plane involution. Each of their marked lines has
order two, so the same facts hold for any generators chosen by the terminal
argument. The full ambient centralizer Sylow orders prove their nonfusion.

Source: Aschbacher–Smith, 15.3.46 and the markings in 15.3.60, printed
pp.1141,1150.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem eq_of_nonidentity_in_two (A : Subgroup G) (hc : Nat.card A = 2)
    {x y : G} (hx : x ∈ A) (hy : y ∈ A) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  obtain ⟨a,_,hall⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hc
  have hx' : (⟨x,hx⟩ : A) ≠ 1 := fun he => hx1 (congrArg Subtype.val he)
  have hy' : (⟨y,hy⟩ : A) ≠ 1 := fun he => hy1 (congrArg Subtype.val he)
  exact congrArg Subtype.val ((hall _ hx').trans (hall _ hy').symm)

omit [Finite G] in
private theorem involution_nonidentity {x : G} (hx : orderOf x = 2) : x ≠ 1 := by
  intro he
  simp [he] at hx

variable (d : CharacteristicTwo.LocalData G)
  (hf : FusionCore.EarlierFusionInputs d.T d.M d.V d.V₁)
include hf

omit hf [Finite G] in
/-- The standard quadratic coordinates retain the original wreath-form value. -/
theorem standard_form_eq_coordinateValue (v : d.V) :
    OrthogonalFourBinary.form
      ((FusionCore.OriginalCoordinates.standardAction d.action).coordinates v).toAdd =
      FusionCore.orthogonalCoordinateValue (d.action.coordinates v) := by
  let := d.action.elementary
  have cert : ∀ a b : ZMod 2, (a=0 ↔ b=0) → a=b := by decide +kernel
  apply cert
  change (FusionCore.OriginalCoordinates.standardAction d.action).singular v ↔ _
  rw [← FusionCore.OriginalCoordinates.quadraticAction_singular,
    FusionCore.OriginalCoordinates.form_eq]

omit hf [Finite G] in
/-- Polar values in the two coordinate conventions agree on the same vectors. -/
theorem standard_polar_eq_coordinateValue (v w : d.V) :
    OrthogonalFourBinary.form.polarBilin
      ((FusionCore.OriginalCoordinates.standardAction d.action).coordinates v).toAdd
      ((FusionCore.OriginalCoordinates.standardAction d.action).coordinates w).toAdd =
    FusionCore.orthogonalCoordinateValue (d.action.coordinates v * d.action.coordinates w) -
      FusionCore.orthogonalCoordinateValue (d.action.coordinates v) -
      FusionCore.orthogonalCoordinateValue (d.action.coordinates w) := by
  rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  change OrthogonalFourBinary.form
      ((FusionCore.OriginalCoordinates.standardAction d.action).coordinates v *
        (FusionCore.OriginalCoordinates.standardAction d.action).coordinates w).toAdd - _ - _ = _
  rw [← map_mul,standard_form_eq_coordinateValue,standard_form_eq_coordinateValue,
    standard_form_eq_coordinateValue,map_mul]

/-- Every generator of the literal central line is singular in the standard
orthogonal action chosen from the original coordinates. -/
theorem marked_point_singular (z : d.V) (hz : orderOf (z : G) = 2)
    (hmark : zpowers (z : G) = d.Z) :
    (FusionCore.OriginalCoordinates.standardAction d.action).singular z := by
  let := d.action.elementary
  obtain ⟨_,c⟩ := FusionCore.orthogonalCoordinateModel_and_fusionCalculations
    (FusionCore.OriginalCoordinates.quadraticAction d.action) hf
    (FusionCore.OriginalCoordinates.plane_definite d.action 1)
  apply (FusionCore.OriginalCoordinates.quadraticAction_singular d.action z).mp
  have he : (z : G) = (c.z : G) := eq_of_nonidentity_in_two d.Z hf.central_order
    (hmark ▸ mem_zpowers (z : G)) c.z_central (involution_nonidentity hz)
    (fun he => c.z_ne_one (Subtype.ext he))
  have he' : z = c.z := Subtype.ext he
  rw [he']
  exact c.z_singular

omit hf [Finite G] in
/-- The literal first coordinate plane is definite in the same action. -/
theorem marked_plane_definite (x : d.V) (hx : (x : G) ∈ d.V₁) (hne : x ≠ 1) :
    ¬ (FusionCore.OriginalCoordinates.standardAction d.action).singular x := by
  let := d.action.elementary
  intro hs
  exact (FusionCore.OriginalCoordinates.plane_definite d.action 1).2.2 x hx hne
    ((FusionCore.OriginalCoordinates.quadraticAction_singular d.action x).mpr hs)

/-- The two source markings stay in distinct ambient conjugacy classes. -/
theorem marked_involutions_not_conjugate (z v : G) (_hz : orderOf z = 2)
    (hv : orderOf v = 2) (hzmark : zpowers z = d.Z)
    (hvmark : zpowers v = d.ZS ⊓ d.V₁) : ¬ IsConj z v := by
  let := d.action.elementary
  obtain ⟨_,c⟩ := FusionCore.orthogonalCoordinateModel_and_fusionCalculations
    (FusionCore.OriginalCoordinates.quadraticAction d.action) hf
    (FusionCore.OriginalCoordinates.plane_definite d.action 1)
  have hline : d.ZS ⊓ d.V₁ = fixedPlane d.V₁ d.S := by
    ext x
    exact ⟨fun h => ⟨h.2,h.1.2⟩,
      fun h => ⟨⟨d.action.plane_le 1 h.1,h.2⟩,h.1⟩⟩
  have he : v = (c.v : G) := eq_of_nonidentity_in_two (fixedPlane d.V₁ d.S)
    (d.action.card_plane_fixed_planeStabilizer d.T d.sylow_le 1)
    (hline ▸ hvmark ▸ mem_zpowers v) (c.fixed_line.symm ▸ mem_zpowers (c.v : G))
    (involution_nonidentity hv) (fun he => c.v_ne_one (Subtype.ext he))
  subst v
  apply FusionCore.not_isConj_of_smaller_centralizer_sylow d.T z (c.v : G) ?_
    c.centralizer_sylow c.sylow_card_lt
  intro t ht
  have hzZ : z ∈ d.Z := hzmark ▸ mem_zpowers z
  exact mem_centralizer_singleton_iff.mpr
    (centralInvolutions_le_centralizer_sylow d.T hzZ t ht)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
