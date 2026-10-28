module
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Mathlib.GroupTheory.Sylow

/-!
# A central four-group with a preserved line

An overgroup of a Sylow two-subgroup acts trivially on a central
four-group if it preserves a subgroup of order two. The automorphism
image fixing the nonidentity point has order at most two. Its Sylow
image is trivial, so the entire image is trivial.

This elementary action argument is used for the original A5 outside
pair in Aschbacher--Smith 13.2.8(1), printed p.880.
-/

open Subgroup
public section
namespace Sylow
variable {G : Type*} [Group G] [Finite G]

theorem centralizes_four_of_preserves_line (T : Sylow 2 G) (N E C : Subgroup G)
    (hTN : (T : Subgroup G) ≤ N)
    (hNE : N ≤ normalizer (E : Set G))
    (hTC : (T : Subgroup G) ≤ centralizer (E : Set G))
    (hCE : C ≤ E) (hC : Nat.card C = 2) (hE : Nat.card E = 4)
    (hNC : N ≤ normalizer (C : Set G)) : N ≤ centralizer (E : Set G) := by
  let f : N →* MulAut E := E.normalizerMonoidHom.comp (inclusion hNE)
  have hCne : C ≠ ⊥ := by intro hh; simp [hh] at hC
  obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne
  let zE : E := ⟨z,hCE z.property⟩
  have hb : Nat.card f.range ≤ 2 := by
    apply card_mulAut_subgroup_le_two_of_fixed_point hE zE
      (fun hh => hz (Subtype.ext (congrArg E.subtype hh)))
    rintro a ⟨n,rfl⟩
    apply Subtype.ext
    change n.val * z.val * n.val⁻¹ = z.val
    exact mul_inv_eq_iff_eq_mul.mpr
      ((normalizer_le_centralizer_of_card_two C hC (hNC n.property)) z z.property).symm
  have hp : IsPGroup 2 f.range := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    have hh : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by omega
    change Nat.card f.range ∣ 2 ^ 1
    rcases hh with hh | hh <;> rw [hh] <;> norm_num
  let S := (T.subtype hTN).mapSurjective f.rangeRestrict_surjective
  have hs : (⊤ : Subgroup f.range) ≤ S := (hp.to_subgroup ⊤).le_sylow_of_normal S
  intro n hn e he
  obtain ⟨t,ht,htn⟩ := hs (show f.rangeRestrict ⟨n,hn⟩ ∈ (⊤ : Subgroup f.range) from mem_top _)
  have heq := congrArg (fun a : f.range => (a.val ⟨e,he⟩ : G)) htn
  change t.val * e * t.val⁻¹ = n * e * n⁻¹ at heq
  have hte : t.val * e * t.val⁻¹ = e := mul_inv_eq_iff_eq_mul.mpr (hTC ht e he).symm
  exact (mul_inv_eq_iff_eq_mul.mp (heq.symm.trans hte)).symm

end Sylow
