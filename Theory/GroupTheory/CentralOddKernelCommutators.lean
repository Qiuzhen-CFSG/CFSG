module

public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import Theory.GroupTheory.CentralCoprimeCardLift
public import Mathlib.Tactic.Group

/-!
# Commutator rigidity for central extensions with odd kernel

Commutators are independent of the chosen lifts. A conjugation that exchanges
two commuting images therefore inverts their central commutator; an odd kernel
forces it to vanish. The same argument identifies two lifts inverted by one
conjugation. Sign actions on commutators provide the compatible root lifts used
in the degree-four Steinberg relations.

Source application: Steinberg, *Lectures on Chevalley Groups*, §6, and the
odd linear central covers in Aschbacher–Smith, Theorem A, §A.2.
-/

open scoped commutatorElement
namespace CentralExtension.OddKernel
open Subgroup
variable {E B : Type*} [Group E] [Group B]

public theorem commute_commutator_of_image_commute (f : E →* B)
    (hc : f.ker ≤ center E) {a b c : E}
    (hab : Commute (f a) (f b)) (hac : Commute (f a) (f c)) :
    Commute a ⁅b,c⁆ := by
  have hb : f (a*b*a⁻¹) = f b := by
    rw [map_mul,map_mul,map_inv,hab.eq,mul_inv_cancel_right]
  have hd : f (a*c*a⁻¹) = f c := by
    rw [map_mul,map_mul,map_inv,hac.eq,mul_inv_cancel_right]
  have hh := CentralExtension.commutator_eq_of_image_eq f hc hb hd
  rw [← conjugate_commutatorElement] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh



public theorem ker_eq_one_of_square (f : E →* B) (hcop : (Nat.card f.ker).Coprime 2)
    {z : E} (hz : z ∈ f.ker) (hz2 : z^2=1) : z=1 := by
  have he : (⟨z,hz⟩ : f.ker)=1 := by
    apply (powCoprime hcop).injective
    exact Subtype.ext (by simpa using hz2)
  exact congrArg Subtype.val he

public theorem commute_of_image_swap (f : E →* B) (hc : f.ker ≤ center E)
    (hcop : (Nat.card f.ker).Coprime 2) {x y t : E}
    (hxy : Commute (f x) (f y))
    (hx : f (t*x*t⁻¹)=f y) (hy : f (t*y*t⁻¹)=f x) : Commute x y := by
  have hk : ⁅x,y⁆ ∈ f.ker := by
    rw [MonoidHom.mem_ker,map_commutatorElement,hxy.commutator_eq]
  have he : ⁅x,y⁆=⁅x,y⁆⁻¹ := by
    have hh := CentralExtension.commutator_eq_of_image_eq f hc hx hy
    rw [← conjugate_commutatorElement,mem_center_iff.mp (hc hk) t,
      mul_inv_cancel_right] at hh
    exact hh.trans (commutatorElement_inv x y).symm
  exact commutatorElement_eq_one_iff_commute.mp (ker_eq_one_of_square f hcop hk (by
    rw [pow_two]
    exact (congrArg (⁅x,y⁆ * ·) he).trans (mul_inv_cancel _)))


public theorem eq_of_image_eq_of_inverted (f : E →* B) (hc : f.ker ≤ center E)
    (hcop : (Nat.card f.ker).Coprime 2) {x y t : E}
    (hxy : f x=f y) (hx : t*x*t⁻¹=x⁻¹) (hy : t*y*t⁻¹=y⁻¹) : x=y := by
  have hk : x*y⁻¹ ∈ f.ker := by simp [MonoidHom.mem_ker,hxy]
  have hcomm : Commute x y := by
    have hz : Commute (x*y⁻¹) y := (mem_center_iff.mp (hc hk) y).symm
    simpa only [inv_mul_cancel_right] using hz.mul_left (Commute.refl y)
  have hh : x*y⁻¹=(x*y⁻¹)⁻¹ := by
    calc
      x*y⁻¹ = t*(x*y⁻¹)*t⁻¹ := by rw [mem_center_iff.mp (hc hk) t,mul_inv_cancel_right]
      _ = (t*x*t⁻¹)*(t*y*t⁻¹)⁻¹ := by group
      _ = x⁻¹*y := by rw [hx,hy,inv_inv]
      _ = (x*y⁻¹)⁻¹ := by rw [mul_inv_rev,inv_inv,hcomm.inv_left.eq]
  apply mul_inv_eq_one.mp
  apply ker_eq_one_of_square f hcop hk
  rw [pow_two]
  exact (congrArg ((x*y⁻¹) * ·) hh).trans (mul_inv_cancel _)

public theorem commutator_inv_left_of_commute {x y : E} (hx : Commute x ⁅x,y⁆) :
    ⁅x⁻¹,y⁆=⁅x,y⁆⁻¹ := by
  rw [commutatorElement_inv_left,← commutatorElement_inv x y,
    (hx.inv_left.inv_right).eq,mul_assoc,inv_mul_cancel,mul_one]

public theorem commutator_inv_right_of_commute {x y : E} (hy : Commute y ⁅x,y⁆) :
    ⁅x,y⁻¹⁆=⁅x,y⁆⁻¹ := by
  rw [commutatorElement_inv_right,← commutatorElement_inv x y,
    (hy.inv_left.inv_right).eq,mul_assoc,inv_mul_cancel,mul_one]

public theorem conjugate_commutator_of_signs (f : E →* B) (hc : f.ker ≤ center E)
    {x y t : E} (hx : Commute x ⁅x,y⁆) (hy : Commute y ⁅x,y⁆)
    (sx sy : Bool)
    (hxt : f (t*x*t⁻¹)=f (if sx then x⁻¹ else x))
    (hyt : f (t*y*t⁻¹)=f (if sy then y⁻¹ else y)) :
    t*⁅x,y⁆*t⁻¹=if sx=sy then ⁅x,y⁆ else ⁅x,y⁆⁻¹ := by
  have he := CentralExtension.commutator_eq_of_image_eq f hc hxt hyt
  rw [← conjugate_commutatorElement] at he
  have hii : ⁅x⁻¹,y⁻¹⁆=⁅x,y⁆ := by
    rw [commutator_inv_left_of_commute (by
      rw [commutator_inv_right_of_commute hy]; exact hx.inv_right),
      commutator_inv_right_of_commute hy,inv_inv]
  cases sx <;> cases sy <;>
    simpa only [Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,
      commutator_inv_left_of_commute hx,commutator_inv_right_of_commute hy,hii] using he

end CentralExtension.OddKernel