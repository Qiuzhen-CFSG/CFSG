module
public import Theory.Representation.FirstCohomology

/-!
# Detecting an inflated cocycle at one element

A cocycle vanishing on the kernel of a surjective group homomorphism
 descends to the actual image group. If vanishing at a specified image
 element detects principal cocycles there, it also detects the original
 cocycle. This retains the given action and quotient map.

Source application: Aschbacher--Smith, 14.3.33(3), printed p.1005,
 the adjustment of the outer element modulo the original seed.
-/

public section
namespace Representation.OneCohomology
variable {k E A W : Type*} [CommRing k] [Group E] [Group A]
  [AddCommGroup W] [Module k W]

/-- Descent and detection of a cocycle through its literal action quotient. -/
theorem principal_of_surjective_of_zero_kernel
    (f : E →* A) (hf : Function.Surjective f) (ρ : Representation k A W)
    (c : cocycles (ρ.comp f)) (hker : ∀ n ∈ f.ker, c.val n = 0)
    (a : E) (ha : c.val a = 0)
    (hdetect : ∀ z : cocycles ρ, z.val (f a) = 0 → ∃ w, principal ρ w = z) :
    ∃ w, ∀ g : E, c.val g = ρ (f g) w - w := by
  classical
  have heq {g t : E} (hgt : f g = f t) : c.val g = c.val t := by
    have hn : t⁻¹ * g ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hgt, inv_mul_cancel]
    have hc := c.property t (t⁻¹ * g)
    rw [mul_inv_cancel_left, hker _ hn, map_zero, zero_add] at hc
    exact hc
  let b (x : A) : E := (hf x).choose
  have hb (x : A) : f (b x) = x := (hf x).choose_spec
  let z : cocycles ρ := ⟨fun x => c.val (b x), by
    intro x y
    have hh := heq (show f (b (x * y)) = f (b x * b y) by rw [map_mul, hb, hb, hb])
    exact hh.trans (by simpa only [MonoidHom.comp_apply, hb] using c.property (b x) (b y))⟩
  have hz : z.val (f a) = 0 := (heq (hb (f a))).trans ha
  obtain ⟨w, hw⟩ := hdetect z hz
  refine ⟨w, fun g => ?_⟩
  have hh := congrArg (fun q : cocycles ρ => q.val (f g)) hw
  exact (heq (hb (f g))).symm.trans hh.symm
end Representation.OneCohomology
