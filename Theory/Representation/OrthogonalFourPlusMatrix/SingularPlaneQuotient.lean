module
public import Theory.Representation.OrthogonalFourPlusMatrix.SingularPlaneNatural

/-!
# The natural quotient by a tensor singular plane

Projection onto the first column has kernel the standard singular plane and
intertwines the first SL₂(4) factor with its natural action. Transport by the
commuting second factor gives the same quotient for the plane generated from
every Sylow fixed line, preserving the original first-factor marking.

Source: Aschbacher--Smith 9.1.2 and the final paragraph of 9.3, printed
pp.729 and734--735. The original-subgroup application is in
GenerationTwoSymplecticNatural.
-/

public noncomputable section
open Matrix Representation Representation.BinaryOffender
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

private def planeQuotient : V →ₗ[ZMod 2] SL2FourNatural.V where
  toFun v := fun i => v i 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem planeQuotient_surjective : Function.Surjective planeQuotient := by
  intro v
  exact ⟨fun i j => if j = 0 then v i else 0, by
    funext i
    change (if (0 : Fin 2) = 0 then v i else 0) = v i
    exact if_pos rfl⟩

private theorem planeQuotient_eq_zero (v : V) : planeQuotient v = 0 ↔ v ∈ plane := by
  constructor
  · intro hv
    refine ⟨fun i => v i 1, ?_⟩
    funext i j
    have hv0 (k : Fin 2) : v k 0 = 0 := congrFun hv k
    fin_cases i <;> fin_cases j <;> simp [planeMap, hv0]
  · rintro ⟨w, rfl⟩
    funext i
    fin_cases i <;> rfl

private theorem planeQuotient_action (a : SL2FourNatural.SL) (v : V) :
    planeQuotient (action (a,1) v) = SL2FourNatural.action a (planeQuotient v) := by
  funext i
  change (action (a,1) v) i 0 = (a.val *ᵥ (fun j => v j 0)) i
  simp only [action_apply, inv_one, SpecialLinearGroup.coe_one, mul_one]
  rfl

private theorem action_mul_apply' (a b : G) (v : V) :
    action (a*b) v = action a (action b v) :=
  congrArg (fun f : Module.End (ZMod 2) V => f v) (action.map_mul a b)

private theorem action_inv_cancel' (g : G) (v : V) : action g (action g⁻¹ v) = v := by
  rw [←action_mul_apply',mul_inv_cancel,map_one]
  rfl

private def planeQuotientMap (g : G) : V →ₗ[ZMod 2] SL2FourNatural.V :=
  planeQuotient.comp (action ((1,g.2) : G)⁻¹)

private theorem planeQuotientMap_surjective (g : G) : Function.Surjective (planeQuotientMap g) := by
  intro w
  obtain ⟨v,hv⟩ := planeQuotient_surjective w
  refine ⟨action (1,g.2) v, ?_⟩
  change planeQuotient (action ((1,g.2) : G)⁻¹ (action (1,g.2) v)) = w
  have he := action_inv_cancel' ((1,g.2) : G)⁻¹ v
  rw [inv_inv] at he
  rw [he,hv]

private theorem planeQuotientMap_eq_zero (g : G) (v : V) :
    planeQuotientMap g v = 0 ↔ v ∈ plane.map (action g) := by
  change planeQuotient (action ((1,g.2) : G)⁻¹ v) = 0 ↔ _
  rw [planeQuotient_eq_zero, plane_map_eq_right]
  constructor
  · intro hv
    refine ⟨action ((1,g.2) : G)⁻¹ v,hv,?_⟩
    exact action_inv_cancel' (1,g.2) v
  · rintro ⟨w,hw,rfl⟩
    have he : action ((1,g.2) : G)⁻¹ (action (1,g.2) w) = w := by
      simpa only [inv_inv] using action_inv_cancel' ((1,g.2) : G)⁻¹ w
    rwa [he]

private theorem planeQuotientMap_action (g : G) (a : SL2FourNatural.SL) (v : V) :
    planeQuotientMap g (action (a,1) v) =
      SL2FourNatural.action a (planeQuotientMap g v) := by
  change planeQuotient (action ((1,g.2) : G)⁻¹ (action (a,1) v)) = _
  rw [←action_mul_apply']
  have he : ((1,g.2) : G)⁻¹*(a,1) = (a,1)*((1,g.2) : G)⁻¹ := by
    apply Prod.ext <;> simp
  rw [he,action_mul_apply',planeQuotient_action]
  rfl

/-- The quotient keeps the literal first-factor action and the entire orbit plane as kernel. -/
theorem sylow_plane_natural_quotient (P : Sylow 2 G) :
    ∃ p : V →ₗ[ZMod 2] SL2FourNatural.V,
      Function.Surjective p ∧
      (∀ v, p v = 0 ↔ v ∈ firstOrbit (fixedSpace action (P : Subgroup G))) ∧
      ∀ (a : SL2FourNatural.SL) (v : V),
        p (action (a,1) v) = SL2FourNatural.action a (p v) := by
  obtain ⟨g,hg⟩ := sylow_fixedSpace_conjugate_point P
  refine ⟨planeQuotientMap g,planeQuotientMap_surjective g,?_,planeQuotientMap_action g⟩
  intro v
  rw [hg,firstOrbit_map,firstOrbit_point_eq_plane]
  exact planeQuotientMap_eq_zero g v

end ClassicalOrthogonal.FourPlusMatrix.Binary
