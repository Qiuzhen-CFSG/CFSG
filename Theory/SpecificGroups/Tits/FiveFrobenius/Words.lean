module

public import Theory.SpecificGroups.Tits.FiveFrobenius.WordCertificate

/-!
# Five-local words and their certified relations

The words are elements of the actual ATLAS subgroup. The cached permutations
are compared to them before checking the elementary-abelian and quaternion
relations and the six conjugation formulas on the five-kernel generators.
Source: ATLAS `TF42G1-max8W1`; see `Tables` for the right-action convention.
-/

namespace Tits.FiveFrobenius
open Atlas1600ParrottData
set_option maxRecDepth 20000

private def a : Atlas1600Group := ⟨atlas1600A, atlas1600A_mem⟩
private def b : Atlas1600Group := ⟨atlas1600B, atlas1600B_mem⟩
private def c : Atlas1600Group := ((a * b) * (a * b ^ 2)) ^ 3
private def x2 : Atlas1600Group := c⁻¹ * b * c
private theorem x2_val : x2.val = x2p := x2p_word.symm

public def u : Atlas1600Group :=
  x2⁻¹ * a⁻¹ * x2 * a⁻¹ * x2 * (a⁻¹ * x2⁻¹) ^ 4

public theorem u_val : u.val = up := by
  change x2.val⁻¹ * a.val⁻¹ * x2.val * a.val⁻¹ * x2.val * (a.val⁻¹ * x2.val⁻¹) ^ 4 = _
  rw [x2_val]
  exact up_word.symm

public def v : Atlas1600Group :=
  x2 * a⁻¹ * x2⁻¹ * (a⁻¹ * x2) ^ 2 * (a⁻¹ * x2⁻¹) ^ 5

public theorem v_val : v.val = vp := by
  change x2.val * a.val⁻¹ * x2.val⁻¹ * (a.val⁻¹ * x2.val) ^ 2 * (a.val⁻¹ * x2.val⁻¹) ^ 5 = _
  rw [x2_val]
  exact vp_word.symm

public def r : Atlas1600Group :=
  (x2⁻¹ * a) ^ 2 * (x2 * a) ^ 2

public theorem r_val : r.val = rp := by
  change (x2.val⁻¹ * a.val) ^ 2 * (x2.val * a.val) ^ 2 = _
  rw [x2_val]
  exact rp_word.symm

public def s : Atlas1600Group :=
  a * x2 * (a * x2⁻¹) ^ 2 * (a * x2) ^ 2 * a * x2⁻¹

public theorem s_val : s.val = sp := by
  change a.val * x2.val * (a.val * x2.val⁻¹) ^ 2 * (a.val * x2.val) ^ 2 * a.val * x2.val⁻¹ = _
  rw [x2_val]
  exact sp_word.symm

public def t : Atlas1600Group :=
  x2 * a * x2 * (a⁻¹ * x2⁻¹) ^ 3 * (a⁻¹ * x2) ^ 2

public theorem t_val : t.val = tp := by
  change x2.val * a.val * x2.val * (a.val⁻¹ * x2.val⁻¹) ^ 3 * (a.val⁻¹ * x2.val) ^ 2 = _
  rw [x2_val]
  exact tp_word.symm

public theorem u_fifth : u ^ 5 = 1 := by
  apply Subtype.ext
  change u.val ^ 5 = 1
  rw [u_val]
  apply Equiv.ext
  exact uMap_order

public theorem v_fifth : v ^ 5 = 1 := by
  apply Subtype.ext
  change v.val ^ 5 = 1
  rw [v_val]
  apply Equiv.ext
  exact vMap_order

public theorem uv_comm : u * v = v * u := by
  apply Subtype.ext
  change u.val * v.val = v.val * u.val
  rw [u_val, v_val]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem r_fourth : r ^ 4 = 1 := by
  apply Subtype.ext
  change r.val ^ 4 = 1
  rw [r_val]
  apply Equiv.ext
  exact rMap_order

public theorem s_square : s ^ 2 = r ^ 2 := by
  apply Subtype.ext
  change s.val ^ 2 = r.val ^ 2
  rw [r_val, s_val]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem t_cube : t ^ 3 = 1 := by
  apply Subtype.ext
  change t.val ^ 3 = 1
  rw [t_val]
  apply Equiv.ext
  exact tMap_order

public theorem s_conj_r : s * r * s⁻¹ = r ^ 3 := by
  apply Subtype.ext
  change s.val * r.val * s.val⁻¹ = r.val ^ 3
  rw [r_val, s_val]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem t_conj_r : t * r * t⁻¹ = r ^ 3 * s := by
  apply Subtype.ext
  change t.val * r.val * t.val⁻¹ = r.val ^ 3 * s.val
  rw [r_val, s_val, t_val]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem t_conj_s : t * s * t⁻¹ = r ^ 3 := by
  apply Subtype.ext
  change t.val * s.val * t.val⁻¹ = r.val ^ 3
  rw [r_val, s_val, t_val]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem r_conj_u : r * u * r⁻¹ = u ^ 2 * v ^ 4 := by
  apply Subtype.ext
  change r.val * u.val * r.val⁻¹ = u.val ^ 2 * v.val ^ 4
  rw [r_val, u_val, v_val]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem r_conj_v : r * v * r⁻¹ = v ^ 3 := by
  apply Subtype.ext
  change r.val * v.val * r.val⁻¹ = v.val ^ 3
  rw [r_val, v_val]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem s_conj_u : s * u * s⁻¹ = u ^ 3 := by
  apply Subtype.ext
  change s.val * u.val * s.val⁻¹ = u.val ^ 3
  rw [s_val, u_val]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem s_conj_v : s * v * s⁻¹ = u ^ 2 * v ^ 2 := by
  apply Subtype.ext
  change s.val * v.val * s.val⁻¹ = u.val ^ 2 * v.val ^ 2
  rw [s_val, u_val, v_val]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem t_conj_u : t * u * t⁻¹ = u * v := by
  apply Subtype.ext
  change t.val * u.val * t.val⁻¹ = u.val * v.val
  rw [t_val, u_val, v_val]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem t_conj_v : t * v * t⁻¹ = u ^ 2 * v ^ 3 := by
  apply Subtype.ext
  change t.val * v.val * t.val⁻¹ = u.val ^ 2 * v.val ^ 3
  rw [t_val, u_val, v_val]
  apply Equiv.ext
  apply allFin
  decide +kernel

end Tits.FiveFrobenius
