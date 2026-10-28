module
public import Theory.GroupTheory.CommutingFactorSwapNorm
/-!
# Involutions in a coset of interchanged commuting factors

Let an involution t interchange commuting factors B and C. An involution
in (BC)t is conjugate by B to an element of (B∩C)t. Write its core part
as bc; conjugating by b removes the B coordinate. The square relation
then forces the remaining C coordinate into B as well.
This retains the actual conjugator needed for the internal fusion step
in Aschbacher, Sporadic Groups (1994),45.10–45.11, pp.248–249.
-/
public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

theorem involution_swap_coset_conjugate_intersection (B C : Subgroup G)
    (hc : ∀ b∈B, ∀ c∈C, b*c=c*b)
    (t : G) (ht : t^2=1) (hs : B.map (MulAut.conj t).toMonoidHom=C)
    (v : G) (hv : v^2=1) (hvt : v*t⁻¹ ∈ B⊔C) :
    ∃ b∈B, b⁻¹*v*b ∈ (B⊓C)⊔zpowers t := by
  have hp : v*t⁻¹ ∈ (B:Set G)*(C:Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right B C
      ((show B≤centralizer (C:Set G) from fun b hb c hc' => (hc b hb c hc').symm).trans
        (centralizer_le_normalizer _))]
    exact hvt
  obtain ⟨b,hb,c,hc',he⟩ := hp
  have hve : v=b*c*t := by
    change b*c=v*t⁻¹ at he
    rw [he]; group
  let r := c*(t*b*t⁻¹)
  have hrC : r∈C := C.mul_mem hc' (hs ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hb)
  have hcon : b⁻¹*v*b=r*t := by rw [hve]; dsimp [r]; group
  have he2 : (r*t)^2=1 := by
    rw [←hcon]
    simpa only [MulAut.conj_apply, inv_inv, hv, map_one] using (map_pow (MulAut.conj b⁻¹) v 2).symm
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht)
  have hri : t*r*t⁻¹=r⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    calc
      r*(t*r*t⁻¹) = (r*t)^2 := by rw [hti]; simp only [pow_two]; group
      _ = 1 := he2
  have htrB : t*r*t⁻¹∈B := by
    rw [←hs] at hrC
    obtain ⟨a,ha,hea⟩ := hrC
    change t*a*t⁻¹=r at hea
    rw [←hea,hti]
    have htt : t*t=1 := by simpa only [pow_two] using ht
    have heq : t*(t*a*t)*t=a := by
      calc
        _ = (t*t)*a*(t*t) := by group
        _ = a := by rw [htt]; simp
    rwa [heq]
  have hrB : r∈B := by
    rw [hri] at htrB
    simpa only [inv_inv] using B.inv_mem htrB
  exact ⟨b,hb,hcon.symm ▸ mul_mem_sup ⟨hrB,hrC⟩ (mem_zpowers t)⟩
end Subgroup
