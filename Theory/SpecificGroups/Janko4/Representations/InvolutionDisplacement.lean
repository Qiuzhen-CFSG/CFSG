module
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.Representation.GeneratedSubgroupInvariants
/-!
# Involution displacement in arbitrary faithful binary J₄ actions

The certified triples generate the actual model from three conjugates of
any involution. Fixed-space intersections bound total codimension by three
times its displacement. The certified order-37 element moves at least
ord₃₇(2)=36 dimensions, so every involution moves at least twelve.
No irreducibility or fixed-free hypothesis is needed.
Source: the native three-conjugate certificates and Aschbacher–Smith C.5.12,
printed p.163, for the remaining A.3.12(17) row.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace Janko4.BinaryDegree
variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
private theorem fixedCodim_sup_bound (ρ : Representation (ZMod 2) G V) (A B : Subgroup G) :
    fixedCodim ρ (A ⊔ B) ≤ fixedCodim ρ A + fixedCodim ρ B := by
  have he : fixedSpace ρ (A ⊔ B) = fixedSpace ρ A ⊓ fixedSpace ρ B := ρ.invariants_comp_sup A B
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpace ρ A) (fixedSpace ρ B)
  have hb := Submodule.finrank_le (fixedSpace ρ A ⊔ fixedSpace ρ B)
  have h1 := fixedCodim_add_finrank ρ A
  have h2 := fixedCodim_add_finrank ρ B
  have h3 := fixedCodim_add_finrank ρ (A ⊔ B)
  rw [he] at h3
  omega
private theorem orderOf_two_thirtySeven : orderOf (2 : ZMod 37) = 36 := by
  apply (orderOf_eq_iff (by decide : 0 < 36)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

theorem twelve_le_fixedCodim_of_involution [Finite G]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (e : G ≃* Janko4.Model) (t : G) (ht : orderOf t = 2) :
    12 ≤ fixedCodim ρ (zpowers t) := by
  have ht' : orderOf (e t) = 2 := (e.orderOf_eq t).trans ht
  have hgen := (Janko4.ThreeConjugates.involutions_generate
    (by intro h; simp [h] at ht') (ht' ▸ pow_orderOf_eq_one (e t))).map e.symm
  rw [e.symm_apply_apply] at hgen
  obtain ⟨g,h,hgen⟩ := hgen
  have h1 := fixedCodim_sup_bound ρ (zpowers t) (zpowers (g*t*g⁻¹))
  have h2 := fixedCodim_sup_bound ρ (zpowers t ⊔ zpowers (g*t*g⁻¹)) (zpowers (h*t*h⁻¹))
  rw [hgen] at h2
  rw [fixedCodim_zpowers_conj] at h1 h2
  let x := e.symm (Janko4.a * Janko4.b)
  have hx : orderOf x = 37 := (e.symm.orderOf_eq _).trans Janko4.orderOf_a_mul_b
  have hlo := prime_order_le_fixedCodim ρ hf (by decide : Nat.Prime 37) (by decide) x hx
  rw [orderOf_two_thirtySeven] at hlo
  have hfix := Submodule.finrank_mono (show fixedSpace ρ ⊤ ≤ fixedSpace ρ (zpowers x) from
    fun v hv g => hv ⟨g,mem_top g⟩)
  have h3 := fixedCodim_add_finrank ρ (zpowers x)
  have h4 := fixedCodim_add_finrank ρ ⊤
  omega
end Janko4.BinaryDegree
