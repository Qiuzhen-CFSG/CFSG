module

public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.RightSupport.Cardinality
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The right perfect support in the J₃ affine three-cover configuration

The literal subgroup `closure {d0, d1}` has order 60, is perfect, and contains
`y`. Its Sylow three-subgroups therefore have order three and are cyclic.
Perfectness follows directly from the four checked power relations: both
products vanish in the abelianization because their orders divide 3 and 5;
then each generator has order dividing 2 and 3 and also vanishes.

These are exactly the three right-support premises of
`ThreeCoverConfig.configurationOfSupports`. This module stays independent
of that assembly and makes no assertion about the left support or about
covering-group ranks. Scalar centralization is already proved in the parent
`ThreeCoverLocalConfiguration.Relations` module.

Source: GLS3 Table 5.3h, printed p.269, the affine local on F₄²;
Aschbacher--Smith A.2.19, printed p.41, and I.2.1, printed p.409.
-/

namespace Sporadic.Janko3.ThreeCoverConfig
open RightCertificate

/-- Both marked generators vanish in the abelianization of their literal closure. -/
public instance right_perfect : Group.IsPerfect rightSupport := by
  let a : rightSupport := ⟨d0, d0_mem⟩
  let b : rightSupport := ⟨d1, d1_mem⟩
  let f : rightSupport →* Abelianization rightSupport := Abelianization.of
  have ha : a ^ 3 = 1 := Subtype.ext d0_cube
  have hb : b ^ 3 = 1 := Subtype.ext d1_cube
  have hab : (a * b) ^ 5 = 1 := Subtype.ext product_fifth
  have hiab : (a⁻¹ * b) ^ 5 = 1 := Subtype.ext inverseProduct_fifth
  have hfa : f a ^ 3 = 1 := by rw [← map_pow, ha, map_one]
  have hfb : f b ^ 3 = 1 := by rw [← map_pow, hb, map_one]
  have hprod3 : (f a * f b) ^ 3 = 1 := by rw [mul_pow, hfa, hfb, one_mul]
  have hprod5 : (f a * f b) ^ 5 = 1 := by
    rw [← map_mul, ← map_pow, hab, map_one]
  have hiprod3 : ((f a)⁻¹ * f b) ^ 3 = 1 := by
    rw [mul_pow, inv_pow, hfa, hfb, inv_one, one_mul]
  have hiprod5 : ((f a)⁻¹ * f b) ^ 5 = 1 := by
    rw [← map_inv, ← map_mul, ← map_pow, hiab, map_one]
  have hp : f a * f b = 1 := orderOf_eq_one_iff.mp <|
    Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 5)
      (orderOf_dvd_of_pow_eq_one hprod3) (orderOf_dvd_of_pow_eq_one hprod5)
  have hip : (f a)⁻¹ * f b = 1 := orderOf_eq_one_iff.mp <|
    Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 5)
      (orderOf_dvd_of_pow_eq_one hiprod3) (orderOf_dvd_of_pow_eq_one hiprod5)
  have heq : f a = f b := inv_mul_eq_one.mp hip
  have ha2 : f a ^ 2 = 1 := by simpa only [← heq, pow_two] using hp
  have ha1 : f a = 1 := orderOf_eq_one_iff.mp <|
    Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
      (orderOf_dvd_of_pow_eq_one ha2) (orderOf_dvd_of_pow_eq_one hfa)
  have hb1 : f b = 1 := heq ▸ ha1
  have hgen : Subgroup.closure ({a, b} : Set rightSupport) = ⊤ := by
    have h : Subgroup.closure (rightSupport.subtype ⁻¹' {d0, d1}) = ⊤ :=
      Subgroup.closure_preimage_eq_top _
    have hs : rightSupport.subtype ⁻¹' {d0, d1} = ({a, b} : Set rightSupport) := by
      ext g
      change (g.val = a.val ∨ g.val = b.val) ↔ (g = a ∨ g = b)
      simp only [Subtype.ext_iff]
    rwa [hs] at h
  constructor
  apply top_unique
  rw [← hgen, Subgroup.closure_le]
  intro g hg
  rw [← Abelianization.ker_of]
  change f g = 1
  rcases hg with rfl | hg
  · exact ha1
  · have he : g = b := hg
    exact he ▸ hb1

/-- Every Sylow three-subgroup of the marked support has prime order. -/
public theorem right_cyclicSylow (S : Sylow 3 rightSupport) : IsCyclic S := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply isCyclic_of_prime_card (p := 3)
  rw [S.card_eq_multiplicity, rightSupport_card]
  decide +kernel

/-- The marked element is the certified word `d1 * d0⁻¹ * d1⁻¹ * d0`. -/
public theorem y_mem_right : y ∈ rightSupport := by
  rw [y_eq_word]
  exact rightSupport.mul_mem
    (rightSupport.mul_mem
      (rightSupport.mul_mem d1_mem (rightSupport.inv_mem d0_mem))
      (rightSupport.inv_mem d1_mem)) d0_mem

end Sporadic.Janko3.ThreeCoverConfig
