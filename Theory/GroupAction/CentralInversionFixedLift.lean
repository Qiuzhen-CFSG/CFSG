module
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

/-!
# Fixed points lift through a centrally inverted quotient

Suppose commuting automorphisms a and b fix an odd central subgroup W,
and a inverts the quotient by W. Every point fixed by b modulo W is
already fixed by b. Its displacement lies in W; applying a and b in the
two orders shows that the displacement squares to one. Oddness kills it.
No coprimality between b and the ambient group is required.

This supplies the literal fixed-point lift on the cubic odd cores in
Aschbacher–Smith I.4.5, printed p.417.
-/

public section
open Subgroup
namespace MulAut
variable {D : Type*} [Group D]

/-- Central inversion forces a commuting actor's fixed cosets to be pointwise fixed. -/
theorem fixed_of_central_displacement_of_inverted_quotient (a b : MulAut D) (hab : a*b=b*a)
    (W : Subgroup D) (hW : W ≤ center D) (hodd : Odd (Nat.card W))
    (hafix : ∀ w ∈ W, a w=w) (hbfix : ∀ w ∈ W, b w=w)
    (hinv : ∀ d, a d*d∈W) (d : D) (hd : b d*d⁻¹∈W) : b d=d := by
  let δ := b d*d⁻¹
  have haδ : a δ=δ := hafix δ hd
  have had : a (b d)=δ*a d := by
    have hh : a (b d)*(a d)⁻¹=δ := by simpa only [δ,map_mul,map_inv] using haδ
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hc : a (b d)=b (a d) := DFunLike.congr_fun hab d
  have hh := hbfix (a d*d) (hinv d)
  rw [map_mul,←hc,had] at hh
  have hbδ : b d=δ*d := by dsimp only [δ]; group
  have hcomm : a d*δ=δ*a d := mem_center_iff.mp (hW hd) (a d)
  have hsq : (⟨δ,hd⟩:W)^2=1 := by
    apply Subtype.ext
    change δ^2=1
    apply mul_right_cancel (b:=a d*d)
    calc
      δ^2*(a d*d)=(δ*a d)*(δ*d) := by
        calc
          _ = δ*(δ*a d)*d := by rw [pow_two]; group
          _ = δ*(a d*δ)*d := by rw [←hcomm]
          _ = _ := by group
      _ = a d*d := by rwa [hbδ] at hh
      _ = 1*(a d*d) := (one_mul _).symm
  have hδone : (⟨δ,hd⟩:W)=1 := hodd.coprime_two_right.pow_left_bijective.injective
    (hsq.trans (one_pow 2).symm)
  exact mul_inv_eq_one.mp (congrArg Subtype.val hδone)

end MulAut
