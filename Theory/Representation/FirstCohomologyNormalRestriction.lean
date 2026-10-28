module
public import Theory.Representation.FirstCohomology
public import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

/-!
# Vanishing of first cohomology from a normal action image

Restrict a cocycle to the normal image and subtract its principal part.
The resulting cocycle vanishes on that image; the cocycle identity and
normality then put every remaining value in its fixed space. Thus a
fixed-point-free normal image with zero first cohomology forces vanishing
for the original representation, even when the defining homomorphism has
kernel.

This is the elementary restriction argument used with the central-cover
construction of Aschbacher--Smith I.1.5, printed p.408. The natural-plus-dual
application is in `BinaryNaturalDual/NormalFirstCohomology`.
-/

public noncomputable section
namespace Representation.OneCohomology
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Vanishing and absence of fixed vectors on a normal image imply vanishing. -/
theorem H1_subsingleton_of_normal_range {D : Type*} [Group D]
    (ρ : Representation k G V) (φ : D →* G) [φ.range.Normal]
    [Subsingleton (H1 (ρ.comp φ))]
    (hfix : fixed (ρ.comp φ) = ⊥) : Subsingleton (H1 ρ) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro f _
  let fD : cocycles (ρ.comp φ) :=
    ⟨fun n => f.val (φ n), fun n m => by simpa only [map_mul, MonoidHom.comp_apply] using f.property (φ n) (φ m)⟩
  obtain ⟨v,hv⟩ := (classMap_eq_zero_iff (ρ.comp φ) fD).mp (Subsingleton.elim _ _)
  let b := f - principal ρ v
  have hbD (n : D) : b.val (φ n) = 0 := by
    change f.val (φ n) - (ρ (φ n) v - v) = 0
    exact sub_eq_zero.mpr (congrArg (fun c : cocycles (ρ.comp φ) => c.val n) hv).symm
  have hb (g : G) : b.val g = 0 := by
    have hm : b.val g ∈ fixed (ρ.comp φ) := by
      intro n
      obtain ⟨m,hm⟩ := (inferInstance : φ.range.Normal).conj_mem (φ n) ⟨n,rfl⟩ g⁻¹
      have he : g * φ m = φ n * g := by rw [hm]; group
      have hc := congrArg b.val he
      rw [b.property g (φ m), b.property (φ n) g, hbD m, hbD n, map_zero, zero_add, add_zero] at hc
      exact hc.symm
    rw [hfix] at hm
    exact hm
  refine ⟨v, ?_⟩
  ext g
  exact (sub_eq_zero.mp (hb g)).symm

end Representation.OneCohomology
