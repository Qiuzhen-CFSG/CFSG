module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Commutator pairings pulled back through central extensions

Lift a homomorphism from an abelian group through a surjective central
extension. Commutators of the lifts give an additive pairing into the
center, independent of every choice of lift. The two commutator product
identities prove additivity because these commutators are central.

This is the elementary central-extension construction used in the defining
root subgroup calculation for PSL₂ (Aschbacher–Smith I.1, GLS3 §6.1).
-/

open scoped commutatorElement IsMulCommutative

namespace CentralExtension

variable {E G A : Type*} [Group E] [Group G] [AddCommGroup A]

private theorem conj_center (g z : E) (hz : z ∈ Subgroup.center E) :
    g*z*g⁻¹ = z := by
  rw [Subgroup.mem_center_iff.mp hz g]
  simp [mul_assoc]

private theorem commutator_mul_center (kx ky x y : E)
    (hkx : kx ∈ Subgroup.center E) (hky : ky ∈ Subgroup.center E) :
    ⁅kx*x, ky*y⁆ = ⁅x,y⁆ := by
  have hc (k : E) (hk : k ∈ Subgroup.center E) (z : E) : Commute k z :=
    (Subgroup.mem_center_iff.mp hk z).symm
  rw [commutatorElement_mul_left_eq_conj_mul,
    (hc kx hkx (ky*y)).commutator_eq, mul_one, (hc kx hkx _).eq,
    mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_mul_right_eq_mul_conj, (hc ky hky x).symm.commutator_eq,
    one_mul, (hc ky hky _).eq, mul_assoc, mul_inv_cancel, mul_one]

/-- Replacing either argument by another lift leaves its commutator unchanged. -/
public theorem commutator_eq_of_image_eq (f : E →* G)
    (hker : f.ker ≤ Subgroup.center E) {x x' y y' : E}
    (hx : f x = f x') (hy : f y = f y') : ⁅x,y⁆ = ⁅x',y'⁆ := by
  have hcx : x*x'⁻¹ ∈ Subgroup.center E := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx, mul_inv_cancel])
  have hcy : y*y'⁻¹ ∈ Subgroup.center E := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy, mul_inv_cancel])
  simpa only [inv_mul_cancel_right] using
    commutator_mul_center (x*x'⁻¹) (y*y'⁻¹) x' y' hcx hcy

/-- The commutators of lifts of an abelian subgroup form an additive pairing
into the ambient center. The formula holds for arbitrary lifts. -/
public theorem exists_lift_commutator_pairing (f : E →* G)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center E)
    (u : Multiplicative A →* G) :
    ∃ B : A →+ A →+ Additive (Subgroup.center E),
      ∀ (x y : A) (a b : E), f a = u (Multiplicative.ofAdd x) →
        f b = u (Multiplicative.ofAdd y) → ((B x y).toMul : E) = ⁅a,b⁆ := by
  let s : A → E := fun a => (hf (u (Multiplicative.ofAdd a))).choose
  have hs (a : A) : f (s a) = u (Multiplicative.ofAdd a) :=
    (hf (u (Multiplicative.ofAdd a))).choose_spec
  have hc (a b : A) : ⁅s a,s b⁆ ∈ Subgroup.center E := by
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, hs, hs]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    rw [← u.map_mul, ← u.map_mul, mul_comm]
  have hzero : f (s 0) = f 1 := by simp [hs]
  have hadd (a b : A) : f (s (a+b)) = f (s a*s b) := by
    rw [map_mul, hs, hs, hs]
    exact u.map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
  let B : A →+ A →+ Additive (Subgroup.center E) := {
    toFun x := {
      toFun y := Additive.ofMul ⟨⁅s x,s y⁆, hc x y⟩
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change ⁅s x,s 0⁆ = 1
        rw [commutator_eq_of_image_eq f hker rfl hzero]
        simp
      map_add' y z := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change ⁅s x,s (y+z)⁆ = ⁅s x,s y⁆ * ⁅s x,s z⁆
        rw [commutator_eq_of_image_eq f hker rfl (hadd y z),
          commutatorElement_mul_right_eq_mul_conj]
        rw [mul_assoc, mul_assoc, ← mul_assoc (s y), conj_center _ _ (hc x z)] }
    map_zero' := by
      apply AddMonoidHom.ext
      intro y
      apply Additive.toMul.injective
      apply Subtype.ext
      change ⁅s 0,s y⁆ = 1
      rw [commutator_eq_of_image_eq f hker hzero rfl]
      simp
    map_add' x y := by
      apply AddMonoidHom.ext
      intro z
      apply Additive.toMul.injective
      apply Subtype.ext
      change ⁅s (x+y),s z⁆ = ⁅s x,s z⁆ * ⁅s y,s z⁆
      rw [commutator_eq_of_image_eq f hker (hadd x y) rfl,
        commutatorElement_mul_left_eq_conj_mul, conj_center _ _ (hc y z)]
      exact (Subgroup.mem_center_iff.mp (hc y z) _).symm }
  refine ⟨B, ?_⟩
  intro x y a b ha hb
  exact commutator_eq_of_image_eq f hker ((hs x).trans ha.symm) ((hs y).trans hb.symm)

end CentralExtension
