module
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Generation under a full natural linear action

A seed containing the coordinate kernel and a nonzero quotient vector generates
the whole numerator under any subgroup inducing the full linear group. Extend
an isomorphism between one-dimensional spans to move that vector to any other
nonzero vector, then lift the full coordinate image through the original kernel.

Source application: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(3), printed p.964, U_H = ⟨V₃^{K₂}⟩.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H W}

/-- A seed larger than the kernel generates the entire section under a full linear actor. -/
theorem conjugateSpan_eq_of_surjective_linear_action
    (d : BinaryConjugationSection H U Z ρ)
    (K B : Subgroup G) (hKH : K ≤ H) (hBU : B ≤ U) (hZB : Z ≤ B)
    (hBZ : ¬ B ≤ Z) (π : K →* (W ≃ₗ[ZMod 2] W)) (hπ : Function.Surjective π)
    (hact : ∀ k w, ρ (inclusion hKH k) w = π k w) :
    conjugateSpanBy B K = U := by
  let S := conjugateSpanBy B K
  have hSU : S ≤ U := conjugateSpanBy_le hBU (hKH.trans d.normalized)
  have hBS : B ≤ S := le_conjugateSpanBy _ _
  obtain ⟨b,hb,hbz⟩ := SetLike.not_le_iff_exists.mp hBZ
  let bU : U := ⟨b,hBU hb⟩
  let v := (d.coordinates bU).toAdd
  have hv : v ≠ 0 := fun hh => hbz ((d.coordinates_eq_one_iff bU).mp hh)
  have hvS : v ∈ d.imageSpace S := (d.mem_imageSpace_iff S v).mpr ⟨bU,hBS hb,rfl⟩
  have htop : d.imageSpace S = ⊤ := by
    apply top_unique
    intro w _
    by_cases hw : w = 0
    · rw [hw]; exact Submodule.zero_mem _
    let ev := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) W v hv
    let ew := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) W w hw
    obtain ⟨a,ha⟩ := Submodule.exists_linearEquiv_restrict_eq (ev.symm.trans ew)
    have hav : a v = w := by
      have hh := ha (ev 1)
      simp only [LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] at hh
      simpa [ev,ew] using hh.symm
    obtain ⟨k,hk⟩ := hπ a
    have hh := d.imageSpace_apply_mem S (inclusion hKH k)
      (le_normalizer_conjugateSpanBy _ _ k.property) v hvS
    rwa [hact,hk,hav] at hh
  apply le_antisymm hSU
  exact (d.le_sup_kernel_of_image_top S htop).trans (sup_le le_rfl (hZB.trans hBS))
end Representation.BinaryConjugationSection
