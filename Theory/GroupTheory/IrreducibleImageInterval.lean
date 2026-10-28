module
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Invariant intervals under a homomorphism

If the image of D is irreducible under the image of R, every R-invariant
subgroup between D intersect ker(f) and D is an endpoint. The proof maps
the subgroup and lifts the resulting equality using the exact kernel.

Source application: conjugation and the faithful action quotient in
Aschbacher--Smith 12.9.4, printed p.860.
-/

public section
open Subgroup
namespace Subgroup
variable {G Q : Type*} [Group G] [Group Q]

/-- Lift irreducibility using the actual kernel on the larger subgroup. -/
theorem interval_of_irreducible_image
    (f : G →* Q) (R D K : Subgroup G) (hker : D ⊓ f.ker = K)
    (hirr : ∀ A : Subgroup Q, A ≤ D.map f →
      R.map f ≤ normalizer (A : Set Q) → A = ⊥ ∨ A = D.map f)
    (A : Subgroup G) (hKA : K ≤ A) (hAD : A ≤ D)
    (hRA : R ≤ normalizer (A : Set G)) : A = K ∨ A = D := by
  rcases hirr (A.map f) (map_mono hAD)
    ((map_mono hRA).trans (A.le_normalizer_map f)) with hA | hA
  · left
    exact le_antisymm ((le_inf hAD ((map_eq_bot_iff A).mp hA)).trans hker.le) hKA
  · right
    apply le_antisymm hAD
    intro d hd
    obtain ⟨a,ha,hea⟩ := hA.symm ▸ (mem_map_of_mem f hd)
    have hda : d / a ∈ K := hker ▸ (show d / a ∈ D ⊓ f.ker from
      ⟨D.div_mem hd (hAD ha),by change f (d / a) = 1; rw [map_div,hea,div_self']⟩)
    simpa only [div_mul_cancel] using A.mul_mem (hKA hda) ha

end Subgroup
