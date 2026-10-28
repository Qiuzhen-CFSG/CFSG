module

public import Theory.GroupTheory.NormalizingInvolutionCard
import Mathlib.Tactic

/-!
# Involutions in a marked semidihedral group of order sixteen

For an order-eight rotation a and involutory reflector b with bab⁻¹=a³,
every square-one element of their join lies in any subgroup containing
a² and b. Write the element as aⁱ or aⁱb; its square forces i to be even.
This keeps the literal native generators in the mixed PSL₂(25) source
application of Aschbacher--Smith J.5.5(4), printed p.447.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Semidihedral

theorem square_one_mem_of_pair {G : Type*} [Group G]
    (a b : G) (ha : orderOf a=8) (hb : b^2=1) (hab : b*a*b⁻¹=a^3)
    (N : Subgroup G) (haN : a^2∈N) (hbN : b∈N)
    {x : G} (hx : x∈zpowers a⊔zpowers b) (hx2 : x^2=1) : x∈N := by
  classical
  have hnorm : b∈normalizer (zpowers a : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (b*a*b⁻¹)=zpowers a
    rw [hab]
    apply le_antisymm
    · exact zpowers_le.mpr ((zpowers a).pow_mem (mem_zpowers a) 3)
    · apply zpowers_le.mpr
      have he : (a^3)^3=a := by
        rw [←pow_mul,show 3*3=8+1 from rfl,pow_succ,←ha,pow_orderOf_eq_one,one_mul]
      have hh := (zpowers (a^3)).pow_mem (mem_zpowers _) 3
      rwa [he] at hh
  have hprod : x∈(zpowers a : Set G)*(zpowers b : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left (zpowers a) (zpowers b) (zpowers_le.mpr hnorm)]
    exact hx
  obtain ⟨y,hy,z,hz,rfl⟩ := hprod
  change y∈zpowers a at hy
  change z∈zpowers b at hz
  have hfin : IsOfFinOrder a := orderOf_pos_iff.mp (by omega)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf,ha] at hy
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
  have hi8 := Finset.mem_range.mp hi
  have hzcases : z=1 ∨ z=b := by
    have hbf : IsOfFinOrder b := isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,hb⟩
    rw [hbf.mem_zpowers_iff_mem_range_orderOf] at hz
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
    have hjlt := Finset.mem_range.mp hj
    have hble := Nat.le_of_dvd (by decide : 0<2) (orderOf_dvd_iff_pow_eq_one.mpr hb)
    have hjcase : j=0 ∨ j=1 := by omega
    rcases hjcase with rfl|rfl <;> simp
  have heven : ∃j:ℕ,i=2*j := by
    rcases hzcases with hz1|hzb
    · rw [hz1] at hx2
      simp only [mul_one,←pow_mul] at hx2
      have hd := orderOf_dvd_iff_pow_eq_one.mpr hx2
      rw [ha] at hd
      refine ⟨i/2,?_⟩
      omega
    · rw [hzb] at hx2
      have he : (a^i*b)^2=a^(4*i) := by
        have hh : b*a^i*b⁻¹=(a^3)^i := by rw [←conj_pow,hab]
        calc
          (a^i*b)^2=a^i*(b*a^i*b⁻¹)*b^2 := by simp only [pow_two];group
          _=a^i*(a^3)^i := by rw [hh,hb,mul_one]
          _=a^(4*i) := by rw [←pow_mul,←pow_add];congr 1;omega
      rw [he] at hx2
      have hd := orderOf_dvd_iff_pow_eq_one.mpr hx2
      rw [ha] at hd
      refine ⟨i/2,?_⟩
      omega
  obtain ⟨j,rfl⟩ := heven
  have hain : a^(2*j)∈N := by rw [pow_mul];exact N.pow_mem haN j
  exact N.mul_mem hain (hzcases.elim (fun h=>h ▸ N.one_mem) (fun h=>h ▸ hbN))
end Semidihedral
