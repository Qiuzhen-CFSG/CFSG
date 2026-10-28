module
public import Theory.Representation.OrthogonalFourPlusMatrix.SingularPlaneOrbit

/-!
# The pointwise stabilizer of a tensor singular plane

An element (a,b) fixing the matrices with zero first column has a=1 and
b upper unipotent. This follows by applying the intertwining equation to
the two standard columns; det(a)=1 and characteristic two eliminate the
possible scalar. Its square is therefore one. Conjugation transports both
the first-projection and square bounds to every Sylow singular plane.

Source application: Aschbacher–Smith9.3.5(1), combined manuscript, printed
p.733. An original cubic Cartan inside the tensor orbit must move its plane.
-/

@[expose] public noncomputable section
open Matrix Representation Representation.BinaryOffender
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

private theorem plane_fixed_entries (g : G)
    (hg : ∀ v ∈ plane, action g v = v) :
    g.1 = 1 ∧ g.2.val 0 0 = 1 ∧ g.2.val 1 0 = 0 ∧ g.2.val 1 1 = 1 := by
  have h0 := (Displacement.fixed_iff_intertwines g _).mp
    (hg (planeMap ![1,0]) ⟨![1,0],rfl⟩)
  have h1 := (Displacement.fixed_iff_intertwines g _).mp
    (hg (planeMap ![0,1]) ⟨![0,1],rfl⟩)
  have ha00 : g.1.val 0 0 = g.2.val 1 1 := by
    simpa [planeMap,mul_apply,Fin.sum_univ_two] using congrArg (fun v : V => v 0 1) h0
  have ha10 : g.1.val 1 0 = 0 := by
    simpa [planeMap,mul_apply,Fin.sum_univ_two] using congrArg (fun v : V => v 1 1) h0
  have ha01 : g.1.val 0 1 = 0 := by
    simpa [planeMap,mul_apply,Fin.sum_univ_two] using congrArg (fun v : V => v 0 1) h1
  have ha11 : g.1.val 1 1 = g.2.val 1 1 := by
    simpa [planeMap,mul_apply,Fin.sum_univ_two] using congrArg (fun v : V => v 1 1) h1
  have hb10 : g.2.val 1 0 = 0 := by
    simpa [planeMap,mul_apply,Fin.sum_univ_two] using (congrArg (fun v : V => v 0 0) h0).symm
  have hsq : (g.2.val 1 1)^2 = 1 := by
    simpa only [det_fin_two,ha00,ha01,ha10,ha11,pow_two,zero_mul,sub_zero] using g.1.det_coe
  have hb11 : g.2.val 1 1 = 1 := by
    simpa only [sq_eq_one_iff,CharTwo.neg_eq,or_self] using hsq
  have hb00 : g.2.val 0 0 = 1 := by
    simpa only [det_fin_two,hb10,hb11,mul_one,mul_zero,sub_zero] using g.2.det_coe
  refine ⟨?_,hb00,hb10,hb11⟩
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [ha00,ha01,ha10,ha11,hb11]

theorem first_eq_one_of_plane_fixed (g : G)
    (hg : ∀ v ∈ plane, action g v = v) : g.1 = 1 :=
  (plane_fixed_entries g hg).1

theorem square_eq_one_of_plane_fixed (g : G)
    (hg : ∀ v ∈ plane, action g v = v) : g^2 = 1 := by
  obtain ⟨ha,h00,h10,h11⟩ := plane_fixed_entries g hg
  apply Prod.ext
  · change g.1^2 = 1
    rw [ha,one_pow]
  · change g.2^2 = 1
    apply Subtype.ext
    rw [pow_two,SpecialLinearGroup.coe_mul,SpecialLinearGroup.coe_one]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply,Fin.sum_univ_two,h00,h10,h11,CharTwo.add_self_eq_zero]

private theorem action_mul_apply (a b : G) (v : V) :
    action (a*b) v = action a (action b v) :=
  congrArg (fun f : Module.End (ZMod 2) V => f v) (action.map_mul a b)

private theorem plane_fixed_of_map_fixed (a g : G)
    (ha : ∀ v ∈ plane.map (action g), action a v = v) :
    ∀ v ∈ plane, action (g⁻¹*a*g) v = v := by
  intro v hv
  have he := congrArg (action g⁻¹) (ha (action g v) ⟨v,hv,rfl⟩)
  rw [←action_mul_apply,←action_mul_apply,←action_mul_apply,inv_mul_cancel,action.map_one] at he
  exact he

theorem first_eq_one_of_sylow_plane_fixed (P : Sylow 2 G) (a : G)
    (ha : ∀ v ∈ firstOrbit (fixedSpace action (P : Subgroup G)), action a v = v) : a.1 = 1 := by
  obtain ⟨g,hg⟩ := sylow_fixedSpace_conjugate_point P
  rw [hg,firstOrbit_map,firstOrbit_point_eq_plane] at ha
  have he := first_eq_one_of_plane_fixed (g⁻¹*a*g) (plane_fixed_of_map_fixed a g ha)
  change g.1⁻¹*a.1*g.1 = 1 at he
  have hh := congrArg (fun b => g.1*b*g.1⁻¹) he
  simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,mul_inv_cancel_right,
    one_mul,mul_one,mul_inv_cancel] using hh

theorem square_eq_one_of_sylow_plane_fixed (P : Sylow 2 G) (a : G)
    (ha : ∀ v ∈ firstOrbit (fixedSpace action (P : Subgroup G)), action a v = v) : a^2 = 1 := by
  obtain ⟨g,hg⟩ := sylow_fixedSpace_conjugate_point P
  rw [hg,firstOrbit_map,firstOrbit_point_eq_plane] at ha
  have he := square_eq_one_of_plane_fixed (g⁻¹*a*g) (plane_fixed_of_map_fixed a g ha)
  have hh := congrArg (fun b => g*b*g⁻¹) he
  calc
    a^2 = g*((g⁻¹*a*g)^2)*g⁻¹ := by simp only [pow_two]; group
    _ = 1 := by simpa using hh

end ClassicalOrthogonal.FourPlusMatrix.Binary

