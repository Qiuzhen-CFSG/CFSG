module
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A cubic automorphism with displacement of order three

On an abelian group of order 27, a cubic automorphism with nine fixed
points fixes its displacement subgroup pointwise. The displacement map
is a homomorphism with image of order three. The induced automorphism of
that image has order dividing both three and two, hence is trivial.

The application in `G2Recognition.PairedCoreSylow` identifies the derived
line of the actual order-81 extensions in Aschbacher–Smith I.4.5, printed
p.417. No elementary-abelian hypothesis or choice of coordinates is needed.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace MulAut
variable {D : Type*} [Group D] [Finite D] [IsMulCommutative D]

theorem cubic_displacement_fixed_of_card_twentySeven
    (b : MulAut D) (hb : b^3=1) (hc : Nat.card D=27)
    (hf : Nat.card b.fixedSubgroup=9) (d : D) :
    b (b d*d⁻¹)=b d*d⁻¹ := by
  let : CommGroup D := IsMulCommutative.instCommGroup
  let f : D →* D := b.toMonoidHom * (MonoidHom.id D)⁻¹
  have hker : f.ker=b.fixedSubgroup := by
    ext x
    rw [MonoidHom.mem_ker,MulAut.mem_fixedSubgroup]
    change b x*x⁻¹=1 ↔ b x=x
    exact mul_inv_eq_one
  have hcard : Nat.card f.range=3 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,hker,hf,hc] at hh
    omega
  have hpres (x : D) : x ∈ f.range ↔ b x ∈ f.range := by
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨b y,by change b (b y)*(b y)⁻¹=b (b y*y⁻¹); simp only [map_mul,map_inv]⟩
    · rintro ⟨y,hy⟩
      refine ⟨b.symm y,?_⟩
      apply b.injective
      change b (b (b.symm y)*(b.symm y)⁻¹)=b x
      simpa only [map_mul,map_inv,b.apply_symm_apply] using
        (show b y*y⁻¹=b x from hy)
  let a : MulAut f.range := {
    toFun x := ⟨b x,(hpres x).mp x.property⟩
    invFun x := ⟨b.symm x,(hpres _).mpr (by simpa only [b.apply_symm_apply] using x.property)⟩
    left_inv x := Subtype.ext (b.symm_apply_apply x)
    right_inv x := Subtype.ext (b.apply_symm_apply x)
    map_mul' x y := Subtype.ext (map_mul b (x:D) (y:D)) }
  have ha3 : a^3=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun hb (x:D)
  let : IsCyclic f.range := isCyclic_of_prime_card hcard
  have ha2 : a^2=1 := by
    have hh := pow_card_eq_one' (x := a)
    rwa [IsCyclic.card_mulAut,hcard,show Nat.totient 3=2 from rfl] at hh
  have ha : a=1 := by
    have hh := ha3
    rw [pow_succ,ha2,one_mul] at hh
    exact hh
  exact congrArg Subtype.val (DFunLike.congr_fun ha ⟨f d,⟨d,rfl⟩⟩)
end MulAut
