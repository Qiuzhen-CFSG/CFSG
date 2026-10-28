module
public import Theory.GroupTheory.DihedralCentralCorrection

/-!
# The cubic-orbit correction word

Two involutions reversing an element of order dividing three have a product
which commutes with that cubic element.  If the adjusted word fixes the three
orbit points and the corresponding kernel is elementary abelian, the order
twelve alternative for the product is impossible.  This is the group-action
calculation used in the binary DGS source branch.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G V : Type*} [Group G] [MulAction G V]

/-- Two involutions reversing a cubic orbit have their adjusted product in its
pointwise stabilizer. -/
theorem inverted_cubic_orbit_product_fixes (r t d : G) (a : V)
    (hd : d^3=1) (hr2 : r*r=1) (ht2 : t*t=1)
    (hrd : r*d*r⁻¹=d⁻¹) (htd : t*d*t⁻¹=d⁻¹)
    (hr : r • a=a) (ht : t • (d⁻¹ • a)=d⁻¹ • a) :
    Commute (r*t) d ∧
      (r*t*d) • a=a ∧ (r*t*d) • (d • a)=d • a ∧
      (r*t*d) • (d⁻¹ • a)=d⁻¹ • a := by
  have hir : r⁻¹=r := inv_eq_of_mul_eq_one_right hr2
  have hit : t⁻¹=t := inv_eq_of_mul_eq_one_right ht2
  have hrd0 : r*d=d⁻¹*r := by
    calc r*d = (r*d*r⁻¹)*r := by simp
         _ = d⁻¹*r := by rw [hrd]
  have htd0 : t*d=d⁻¹*t := by
    calc t*d = (t*d*t⁻¹)*t := by simp
         _ = d⁻¹*t := by rw [htd]
  have hrd' : r*d⁻¹=d*r := by
    have hconj : r*d⁻¹*r=d := by
      calc
        r*d⁻¹*r = r*(d⁻¹*r) := by rw [mul_assoc]
        _ = r*(r*d) := by rw [← hrd0]
        _ = d := by rw [← mul_assoc, hr2, one_mul]
    calc
      r*d⁻¹ = r*d⁻¹*(r*r) := by rw [hr2, mul_one]
      _ = (r*d⁻¹*r)*r := by simp [mul_assoc]
      _ = d*r := by rw [hconj]
  have htd' : t*d⁻¹=d*t := by
    have hconj : t*d⁻¹*t=d := by
      calc
        t*d⁻¹*t = t*(d⁻¹*t) := by rw [mul_assoc]
        _ = t*(t*d) := by rw [← htd0]
        _ = d := by rw [← mul_assoc, ht2, one_mul]
    calc
      t*d⁻¹ = t*d⁻¹*(t*t) := by rw [ht2, mul_one]
      _ = (t*d⁻¹*t)*t := by simp [mul_assoc]
      _ = d*t := by rw [hconj]
  have hc : Commute (r*t) d := by
    change (r*t)*d=d*(r*t)
    rw [mul_assoc,htd0,←mul_assoc,hrd',mul_assoc]
  have hd2 : d⁻¹*d⁻¹=d := by
    apply mul_left_cancel (a := d*d)
    calc
      (d*d)*(d⁻¹*d⁻¹)=1 := by group
      _ = (d*d)*d := by simpa only [pow_succ,pow_zero,one_mul] using hd.symm
  have hda : d • a=d⁻¹ • (d⁻¹ • a) := by rw [←mul_smul,hd2]
  have hbase : (r*t*d) • a=a := by
    rw [mul_smul,mul_smul,hda,←mul_smul t,htd',mul_smul,ht,smul_inv_smul,hr]
  have hc' : Commute (r*t*d) d := hc.mul_left (Commute.refl d)
  refine ⟨hc,hbase,?_,?_⟩
  · rw [←mul_smul,hc'.eq,mul_smul,hbase]
  · rw [←mul_smul,hc'.inv_right.eq,mul_smul,hbase]

/-- An exponent-two kernel on that cubic orbit excludes product order twelve
and contains the exact central correction word. -/
theorem cubic_orbit_product_six (r t d : G) (a : V) (Z : Subgroup G)
    (hd : d^3=1) (hr2 : r*r=1) (ht2 : t*t=1)
    (hrd : r*d*r⁻¹=d⁻¹) (htd : t*d*t⁻¹=d⁻¹)
    (hr : r • a=a) (ht : t • (d⁻¹ • a)=d⁻¹ • a)
    (hkernel : ∀ g : G, g • a=a → g • (d • a)=d • a →
      g • (d⁻¹ • a)=d⁻¹ • a → g∈Z)
    (hZ : ∀ z∈Z, z*z=1)
    (horder : orderOf (r*t)=6 ∨ orderOf (r*t)=12) :
    orderOf (r*t)=6 ∧ (r*t)^3∈Z := by
  obtain ⟨hc,h₀,h₁,h₂⟩ := inverted_cubic_orbit_product_fixes r t d a hd hr2 ht2 hrd htd hr ht
  have hg : r*t*d∈Z := hkernel _ h₀ h₁ h₂
  have hcube : (r*t*d)^3=(r*t)^3 := by rw [hc.mul_pow,hd,mul_one]
  have hz : (r*t)^3∈Z := hcube ▸ Z.pow_mem hg 3
  have hp : (r*t)^6=1 := by
    calc
      (r*t)^6 = (r*t)^3*(r*t)^3 := (pow_add (r*t) 3 3)
      _ = 1 := hZ _ hz
  refine ⟨?_,hz⟩
  rcases horder with h | h
  · exact h
  · have hh := orderOf_dvd_of_pow_eq_one hp
    norm_num [h] at hh

end Theory.GroupTheory
