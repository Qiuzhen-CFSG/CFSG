module
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.TorusSplitting
public import Theory.SpecificGroups.PSL3.SmallCompletion.Weyl
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Odd Weyl products from Sylow involution centralizers

Suppose every involution centralizer normalizes an ambient Sylow two-subgroup.
Two involutions normalizing an odd subgroup cannot have even-order product
when the product's cube centralizes that subgroup and the first involution
acts nontrivially. The central involution in the dihedral rotation subgroup
would force this first involution into a normal Sylow subgroup; coprime
intersection would then make its action trivial.

The matrix calculation verifies nontriviality for both simple reflections on
the full projective diagonal torus, retaining the cubic scalar kernel and
field four. This gives the parity step of the linear F.4.49 argument directly
from F.4.46(2), without the separate F.4.47 centralizer classification.
Source: Aschbacher–Smith, F.4.46–49, printed pp.297–299.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement MatrixGroups
namespace Matrix.PSL3.LinearAmbientGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The cubic action on an odd torus excludes an even Weyl product when
involution centralizers normalize ambient Sylow two-subgroups. -/
theorem odd_weyl_product
    (hC : ∀ z : G, orderOf z = 2 → ∃ P : Sylow 2 G,
      centralizer ({z} : Set G) ≤ normalizer (P : Set G))
    (D : Subgroup G) (hD : Odd (Nat.card D)) (s t : G)
    (hs : s^2=1) (ht : t^2=1)
    (hsD : s ∈ normalizer (D : Set G))
    (hsC : s ∉ centralizer (D : Set G))
    (hact : (s*t)^3 ∈ centralizer (D : Set G)) : Odd (orderOf (s*t)) := by
  by_contra heven
  have htwo : 2 ∣ orderOf (s*t) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp heven)
  let j := (s*t)^(orderOf (s*t)/2)
  have hj : orderOf j=2 := orderOf_pow_orderOf_div (orderOf_pos _).ne' htwo
  have hj2 : j^2=1 := hj ▸ pow_orderOf_eq_one j
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs)
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ht)
  have hji : j⁻¹=j := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hj2)
  have hsconj : s*(s*t)*s⁻¹=(s*t)⁻¹ := by
    simp only [_root_.mul_inv_rev,hsi,hti,←mul_assoc,←pow_two,hs,one_mul]
  have hsj : s ∈ centralizer ({j} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      s*j*s⁻¹ = (s*(s*t)*s⁻¹)^(orderOf (s*t)/2) := map_pow (MulAut.conj s) _ _
      _ = j⁻¹ := by rw [hsconj,inv_pow]
      _ = j := hji
  have hjC : j ∈ centralizer (D : Set G) := by
    have hh := (centralizer (D : Set G)).pow_mem hact (orderOf (s*t)/2)
    have he : ((s*t)^3)^(orderOf (s*t)/2)=j^3 := by
      dsimp [j]
      rw [←pow_mul,←pow_mul,Nat.mul_comm]
    rw [he,pow_succ,hj2,one_mul] at hh
    exact hh
  obtain ⟨P,hP⟩ := hC j hj
  have hs1 : s ≠ 1 := by intro hh; exact hsC (hh ▸ (centralizer _).one_mem)
  have hsord : orderOf s=2 := orderOf_eq_prime hs hs1
  have hsP : s ∈ (P : Subgroup G) := by
    have hp : IsPGroup 2 (zpowers s) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers,hsord,pow_one])
    exact ((hp.inf_normalizer_sylow P).le ⟨mem_zpowers s,hP hsj⟩).2
  have hDP : D ≤ normalizer (P : Set G) := by
    intro x hx
    exact hP (mem_centralizer_singleton_iff.mpr (hjC x hx))
  have hdis : Disjoint (P : Subgroup G) D :=
    disjoint_of_coprime_natCard (by
      obtain ⟨k,hk⟩ := P.isPGroup'.exists_card_eq
      rw [hk]
      exact hD.coprime_two_left.pow_left k)
  apply hsC
  intro x hx
  have hcommP : ⁅s,x⁆ ∈ (P : Subgroup G) :=
    le_normalizer_iff_commutator_le_left.mp hDP (commutator_mem_commutator hsP hx)
  have hcommD : ⁅s,x⁆ ∈ D := by
    exact D.mul_mem ((mem_normalizer_iff.mp hsD x).mp hx) (D.inv_mem hx)
  exact (commutatorElement_eq_one_iff_mul_comm.mp (disjoint_def.mp hdis hcommP hcommD)).symm
end Matrix.PSL3.LinearAmbientGeometry

namespace Matrix.PSL3.LinearAmbientGeometry
open Matrix.PSL3.SmallCompletion Matrix.PSL3.CartanActions Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

def reflectionParameters (i : Bool) (d : Fˣ × Fˣ) : Fˣ × Fˣ :=
  if i then ((d.1*d.2)⁻¹,d.2) else (d.1,(d.1*d.2)⁻¹)

omit [Finite F] in
theorem reflection_torus_conj (i : Bool) (d : Fˣ × Fˣ) :
    reflection F i * torusMap F d * (reflection F i)⁻¹ =
      torusMap F (reflectionParameters F i d) := by
  change projection F (reflectionSL F i) * projection F (torusSL F d) *
    (projection F (reflectionSL F i))⁻¹ = projection F (torusSL F _)
  rw [←map_inv,←map_mul,←map_mul]
  congr 1
  have hi : (reflectionSL F i)⁻¹=reflectionSL F i :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using reflectionSL_sq F i)
  rw [hi]
  apply Subtype.ext
  change (reflectionSL F i).val * (torusSL F d).val * (reflectionSL F i).val = _
  cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [reflectionParameters,torusSL_val,reflectionSL,Matrix.mul_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_three,mul_comm]

/-- A simple reflection acts nontrivially on the full projective torus,
including when its scalar kernel has order three. -/
theorem reflection_not_centralizes_torus (hq : 2 < Nat.card F) (i : Bool) :
    reflection F i ∉ centralizer (torus F : Set PSL(3,F)) := by
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_units]; omega)
  obtain ⟨a,ha⟩ := exists_ne (1:Fˣ)
  intro hc
  let d : Fˣ × Fˣ := if i then (1,a) else (a,1)
  have he : torusMap F (reflectionParameters F i d) = torusMap F d := by
    rw [←reflection_torus_conj,←hc _ ⟨d,rfl⟩,mul_inv_cancel_right]
  have hone : torusMap F (reflectionParameters F i d * d⁻¹)=1 := by
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hh := (BorelQuotient.torusMap_eq_one_iff F _).mp hone |>.1
  cases i <;> simp [reflectionParameters,d] at hh
  · exact ha hh
  · exact ha hh
end Matrix.PSL3.LinearAmbientGeometry

namespace Matrix.PSL3.LinearAmbientGeometry
variable {G : Type*} [Group G]

/-- An odd-order product of distinct square-one elements supplies an actual
involution interchanging them by conjugation. -/
theorem swapping_involution_of_odd_product
    (s t : G) (hs : s^2=1) (ht : t^2=1) (hne : s≠t)
    (ho : Odd (orderOf (s*t))) :
    ∃ w : G, orderOf w=2 ∧ w*s*w⁻¹=t := by
  obtain ⟨k,hk⟩ := ho
  let r := s*t
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs)
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht)
  have hsr : s*r*s⁻¹=r⁻¹ := by
    dsimp [r]
    simp only [_root_.mul_inv_rev,hsi,hti,←mul_assoc,←pow_two,hs,one_mul]
  have hsk : s*r^k=(r^k)⁻¹*s := by
    apply (mul_inv_eq_iff_eq_mul).mp
    calc
      s*r^k*s⁻¹ = (s*r*s⁻¹)^k := map_pow (MulAut.conj s) r k
      _ = (r^k)⁻¹ := by rw [hsr,inv_pow]
  let w := r^k*s
  have hw2 : w^2=1 := by
    calc
      _ = r^k*(s*r^k)*s := by dsimp [w]; simp only [pow_two]; group
      _ = 1 := by rw [hsk]; simp [←pow_two,hs]
  have hr : r^(k+k)*r=1 := by
    rw [←pow_succ]
    convert pow_orderOf_eq_one r using 1
    dsimp [r]
    congr 1
    omega
  have hr' : r^(k+k)=r⁻¹ := eq_inv_of_mul_eq_one_left hr
  have hws : w*s*w⁻¹=t := by
    have hwi : w⁻¹=w := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hw2)
    rw [hwi]
    calc
      w*s*w = r^k*(s*s)*r^k*s := by dsimp [w]; group
      _ = r^(k+k)*s := by rw [←pow_two,hs,mul_one,←pow_add]
      _ = t := by rw [hr']; simp only [r,_root_.mul_inv_rev,hsi,hti,mul_assoc,←pow_two,hs,mul_one]
  have hw1 : w≠1 := by intro hh; apply hne; simpa only [hh,one_mul,inv_one,mul_one] using hws
  exact ⟨w,orderOf_eq_prime hw2 hw1,hws⟩
end Matrix.PSL3.LinearAmbientGeometry
