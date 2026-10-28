module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

/-!
# Centralizers of involutions exchanging elementary factors

Suppose A and B are elementary two-subgroups, A normalizes B, and every
square-one element of AB lies in A or B. If an involution exchanges A and B
and fixes their intersection pointwise, its fixed subgroup in AB is A ∩ B.
Writing a fixed element as ab shows that it has square one; the involution
cover then places it in both factors. No finiteness or splitting is needed.

Application: Aschbacher--Smith, Quasithin Groups, 14.3.21(2), printed p.998.
-/

public section

open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem elementary_factor_swap_centralizer (A B : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hn : A ≤ normalizer (B : Set G))
    (hmax : ∀ x ∈ A ⊔ B, x ^ 2 = 1 → x ∈ A ∨ x ∈ B)
    (t : G) (ht2 : t ^ 2 = 1) (hs : A.map (MulAut.conj t).toMonoidHom = B)
    (htV : t ∈ centralizer (A ⊓ B : Set G)) :
    (A ⊔ B) ⊓ centralizer ({t} : Set G) = A ⊓ B := by
  let α : MulAut G := MulAut.conj t
  have hα2 (a : G) : α (α a) = a := by
    change t * (t * a * t⁻¹) * t⁻¹ = a
    calc
      _ = (t*t)*a*(t*t)⁻¹ := by group
      _ = a := by rw [←pow_two,ht2]; simp
  have hAB (a : G) (ha : a ∈ A) : α a ∈ B :=
    hs ▸ mem_map_of_mem α.toMonoidHom ha
  have hBA (b : G) (hb : b ∈ B) : α b ∈ A := by
    obtain ⟨a,ha,he⟩ := hs.symm ▸ hb
    change α a = b at he
    rw [←he,hα2]
    exact ha
  have hfix (v : G) (hv : v ∈ A ⊓ B) : α v = v := by
    change t * v * t⁻¹ = v
    exact mul_inv_eq_iff_eq_mul.mpr (htV v hv).symm
  apply le_antisymm
  · intro x hx
    have hαx : α x = x := by
      change t*x*t⁻¹=x
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx.2).symm
    have hxprod : x ∈ (A : Set G) * (B : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right A B hn]
      exact hx.1
    obtain ⟨a,ha,b,hb,rfl⟩ := hxprod
    have ha2 := elemPow_eq_one_of_isElementaryAbelian (p:=2) a ha
    have hb2 := elemPow_eq_one_of_isElementaryAbelian (p:=2) b hb
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ha2)
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hb2)
    have he : α b * α a = b * a := by
      have hh := congrArg Inv.inv hαx
      simpa only [map_mul, mul_inv_rev, ←map_inv, hai, hbi] using hh
    let v := a * α b
    have hvA : v ∈ A := A.mul_mem ha (hBA b hb)
    have hvB : v ∈ B := by
      have hc : a*b*a⁻¹ ∈ B := (mem_normalizer_iff.mp (hn ha) b).mp hb
      have hv : v = (a*b*a⁻¹)*α a := by
        calc
          v = a * (α b * α a) * (α a)⁻¹ := by dsimp [v]; group
          _ = a * (b*a) * (α a)⁻¹ := by rw [he]
          _ = (a*b*a⁻¹)*α a := by rw [←map_inv,hai]; group
      rw [hv]
      exact B.mul_mem hc (hAB a ha)
    have hvf := hfix v ⟨hvA,hvB⟩
    have hbv : b = α a * v := by
      have heq : α a * b = v := by simpa only [v,map_mul,hα2] using hvf
      calc
        b = (α a)⁻¹ * (α a * b) := by group
        _ = α a * v := by rw [heq,←map_inv,hai]
    have hc : Commute a (α a) := by
      have hh := hαx
      rw [hbv,map_mul,map_mul,hα2,hvf] at hh
      exact (mul_right_cancel (by simpa only [mul_assoc] using hh)).symm
    have hcv : Commute (a * α a) v := by
      apply Commute.mul_left
      · exact congrArg Subtype.val (mul_comm (⟨a,ha⟩ : A) ⟨v,hvA⟩)
      · exact congrArg Subtype.val (mul_comm (⟨α a,hAB a ha⟩ : B) ⟨v,hvB⟩)
    have hx2 : (a*b)^2 = 1 := by
      rw [hbv,←mul_assoc,hcv.mul_pow,hc.mul_pow,ha2,
        ←map_pow,ha2,map_one,elemPow_eq_one_of_isElementaryAbelian (p:=2) v hvA]
      simp
    rcases hmax (a*b) hx.1 hx2 with hA | hB
    · exact ⟨hA,hαx ▸ hAB (a*b) hA⟩
    · exact ⟨hαx ▸ hBA (a*b) hB,hB⟩
  · intro x hx
    refine ⟨(show A ≤ A ⊔ B from le_sup_left) hx.1,mem_centralizer_singleton_iff.mpr ?_⟩
    exact htV x hx

end Theory.GroupTheory
