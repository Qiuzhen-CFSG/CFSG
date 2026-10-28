module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Geometry
public import Theory.Representation.BinaryPermutation.SevenParabolic.Extension
import Mathlib.Tactic
/-!
# Compatibility of the source form with seven-point coordinates

The restricted dot product is invariant and nondegenerate. Comparing any
other nondegenerate invariant bilinear form with it gives an invertible
linear map centralizing A₇, hence the identity. Thus an equivariant natural
module identification already preserves the source form: no additional
isometry assumption is required by the Chapter 12 consumer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), §B.3,
G.11.2(4), and Lemma 12.8.13(6), printed pp.856–857.
-/

public section
namespace BinaryPermutation.SevenParabolic

lemma pairing_permute (s : Equiv.Perm (Fin 7)) (v w : Space) :
    pairing (action s v) (action s w) = pairing v w := by
  exact Equiv.sum_comp s.symm (fun i => v.val i * w.val i)

/-- The binary dot product is the unique nondegenerate A₇-invariant bilinear form. -/
lemma invariant_form_unique (B : LinearMap.BilinForm (ZMod 2) Space)
    (hB : B.Nondegenerate)
    (hInv : ∀ g : alternatingGroup (Fin 7), ∀ v w,
      B (action g.val v) (action g.val w) = B v w) : B = pairing := by
  have hp : Function.Injective pairing := LinearMap.ker_eq_bot.mp pairing_nondegenerate.ker_eq_bot
  let eP : Space ≃ₗ[ZMod 2] Module.Dual (ZMod 2) Space :=
    LinearEquiv.ofBijective pairing ⟨hp,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hp⟩
  have hb : Function.Injective B := LinearMap.ker_eq_bot.mp hB.ker_eq_bot
  let eB : Space ≃ₗ[ZMod 2] Module.Dual (ZMod 2) Space :=
    LinearEquiv.ofBijective B ⟨hb,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hb⟩
  let c := eB.trans eP.symm
  have hc (v w : Space) : pairing (c v) w = B v w := by
    exact LinearMap.congr_fun (eP.apply_symm_apply (eB v)) w
  have hc1 : c = 1 := by
    apply linearCentralizer_eq_one
    intro g v
    apply hp
    ext w
    let u := action g.val⁻¹ w
    have hu : action g.val u = w := by
      simp only [u, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    rw [← hu]
    change pairing (c (action g.val v)) (action g.val u) =
      pairing (action g.val (c v)) (action g.val u)
    rw [hc, hInv, pairing_permute, hc]
  ext v w
  have h := hc v w
  rw [hc1] at h
  exact h.symm

/-- An equivariant natural-module identification also identifies its actual
invariant nondegenerate form. No extra isometry hypothesis is needed. -/
lemma marked_form_eq
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    (K : Subgroup A) (ρ : Representation (ZMod 2) A V)
    (eK : K ≃* alternatingGroup (Fin 7)) (eV : V ≃ₗ[ZMod 2] Space)
    (he : ∀ k : K, ∀ v, eV (ρ k v) = action (eK k).val (eV v))
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (hInv : ∀ k : K, ∀ v w, B (ρ k v) (ρ k w) = B v w)
    (v w : V) : B v w = pairing (eV v) (eV w) := by
  have hinv (k : K) (x : Space) :
      eV.symm (action (eK k).val x) = ρ k (eV.symm x) := by
    apply eV.injective
    simp only [eV.apply_symm_apply, he]
  have h := invariant_form_unique (LinearMap.BilinForm.congr eV B) (hB.congr eV) (by
    intro g x y
    obtain ⟨k, rfl⟩ := eK.surjective g
    simp only [LinearMap.BilinForm.congr_apply, hinv, hInv])
  rw [← h]
  simp only [LinearMap.BilinForm.congr_apply, eV.symm_apply_apply]

end BinaryPermutation.SevenParabolic
