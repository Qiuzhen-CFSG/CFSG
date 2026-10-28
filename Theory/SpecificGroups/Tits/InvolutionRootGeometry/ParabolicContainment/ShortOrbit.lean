module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.SecondNormalizer.Characteristic

/-!
# The four Sylow conjugates of the short-root representative

The Sylow subgroup normalizes its known second center E. Each generator
also preserves the coset E s₄, by the existing Parrott relations. Three
kernel-checked word identities identify that coset with the four conjugates
of s₄ used in the ambient coset test. Thus the orbit statement is structural;
no exhaustive computation over the 2048 Sylow elements is needed.

Source: Parrott (1972), §5, printed p.683, with the certified left-action
Atlas marking. The consumer is the short-root centralizer containment.
-/

public section

open Subgroup
namespace Tits.InvolutionRootGeometry.ParabolicContainment
open Atlas1600ParrottData

@[expose] def orbitConjugator (k : Fin 4) : Atlas1600Group :=
  ![1, atlas1600ParrottAssignment .s3, atlas1600ParrottAssignment .s7,
    atlas1600ParrottAssignment .s7 * atlas1600ParrottAssignment .s3] k

@[expose] def shortOrbit (k : Fin 4) : Atlas1600Group :=
  orbitConjugator k * atlas1600ParrottAssignment .s4 * (orbitConjugator k)⁻¹

open RelativeParabolicNormalizers
local notation "z" => atlas1600ParrottAssignment ParrottGenerator.s4
local notation "x" => atlas1600R5
local notation "y" => secondCenterMate
local notation "E" => secondCenter
private theorem val_mul (a b : Atlas1600Group) : (a*b).val = a.val*b.val := rfl
private theorem val_inv (a : Atlas1600Group) : (a⁻¹).val = a.val⁻¹ := rfl
private theorem val_pow (a : Atlas1600Group) (n : ℕ) : (a^n).val = a.val^n := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem orbit_one : shortOrbit 1 = y * z := by
  apply Subtype.ext
  change (atlas1600ParrottAssignment .s3 * z * (atlas1600ParrottAssignment .s3)⁻¹).val = (y*z).val
  simp only [secondCenterMate, val_mul, val_inv, val_pow, atlas1600ParrottAssignment_val]
  apply Equiv.ext
  apply Atlas1600ParrottData.allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem orbit_two : shortOrbit 2 = x * y * z := by
  apply Subtype.ext
  change (atlas1600ParrottAssignment .s7 * z * (atlas1600ParrottAssignment .s7)⁻¹).val = (x*y*z).val
  simp only [secondCenterMate, atlas1600R5_eq, val_mul, val_inv, val_pow, atlas1600ParrottAssignment_val]
  apply Equiv.ext
  apply Atlas1600ParrottData.allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem orbit_three : shortOrbit 3 = x * z := by
  apply Subtype.ext
  change ((atlas1600ParrottAssignment .s7 * atlas1600ParrottAssignment .s3) * z *
    (atlas1600ParrottAssignment .s7 * atlas1600ParrottAssignment .s3)⁻¹).val = (x*z).val
  simp only [atlas1600R5_eq, val_mul, val_inv, val_pow, atlas1600ParrottAssignment_val]
  apply Equiv.ext
  apply Atlas1600ParrottData.allFin
  decide +kernel

private def rootCoset : Set Atlas1600Group := {t | t * z⁻¹ ∈ E}

private theorem normalizes_coset (g : Atlas1600Group)
    (hg : g ∈ normalizer (E : Set Atlas1600Group))
    (hz : g*z*g⁻¹*z⁻¹ ∈ E) : g ∈ normalizer rootCoset := by
  intro t
  change t*z⁻¹ ∈ E ↔ g*t*g⁻¹*z⁻¹ ∈ E
  rw [show g*t*g⁻¹*z⁻¹ = (g*(t*z⁻¹)*g⁻¹)*(g*z*g⁻¹*z⁻¹) by group,
    (E).mul_mem_cancel_right hz]
  exact hg (t*z⁻¹)

private theorem gen_mem (a : ParrottGenerator) (h1 : a ≠ .r1) (h8 : a ≠ .r8) :
    atlas1600ParrottAssignment a ∈ ExceptionalParabolics.S := by
  rw [ExceptionalParabolics.S, atlas1600SylowTwoSubgroup_eq]
  apply subset_closure
  cases a <;> simp_all

private theorem inverse_commuting {a b : Atlas1600Group} (h : b*a*b⁻¹=a) : a*b*a⁻¹=b := by
  have hc := mul_inv_eq_iff_eq_mul.mp h
  rw [← hc, mul_inv_cancel_right]

private theorem generator_coset (a : ParrottGenerator) (h1 : a ≠ .r1) (h8 : a ≠ .r8) :
    atlas1600ParrottAssignment a ∈ normalizer rootCoset := by
  apply normalizes_coset _
    (second_le_normalizer_secondCenter (ExceptionalParabolics.sylow_le_second (gen_mem a h1 h8)))
  have hx : x ∈ E := mem_sup_left (mem_zpowers _)
  have hy : y ∈ E := mem_sup_right (mem_zpowers _)
  have fix (g : Atlas1600Group) (h : g*z*g⁻¹=z) : g*z*g⁻¹*z⁻¹ ∈ E := by
    rw [h, mul_inv_cancel]; exact (E).one_mem
  cases a with
  | r1 => exact (h1 rfl).elim
  | r8 => exact (h8 rfl).elim
  | s1 =>
    apply fix
    apply inverse_commuting
    apply Subtype.ext
    simpa only [val_mul, val_inv, atlas1600ParrottAssignment_val, permutation] using
      Atlas1600SylowTwoCertificate.conjugate_4_1
  | s2 =>
    apply fix
    apply inverse_commuting
    apply Subtype.ext
    simpa only [val_mul, val_inv, atlas1600ParrottAssignment_val, permutation] using
      Atlas1600SylowTwoCertificate.conjugate_4_2
  | s3 =>
    change shortOrbit 1 * z⁻¹ ∈ E
    simpa only [orbit_one, mul_inv_cancel_right] using hy
  | s4 => exact fix _ (by group)
  | s5 =>
    have h : atlas1600ParrottAssignment .s5*z*(atlas1600ParrottAssignment .s5)⁻¹=y*z := by
      apply Subtype.ext
      simpa only [secondCenterMate, val_mul, val_inv, val_pow, atlas1600ParrottAssignment_val, permutation] using
        Atlas1600SylowTwoCertificate.conjugate_5_4
    simpa only [h, mul_inv_cancel_right] using hy
  | s6 =>
    apply fix
    apply Subtype.ext
    simpa only [val_mul, val_inv, atlas1600ParrottAssignment_val, permutation] using
      Atlas1600SylowTwoCertificate.conjugate_6_4
  | s7 =>
    change shortOrbit 2 * z⁻¹ ∈ E
    simpa only [orbit_two, mul_inv_cancel_right] using (E).mul_mem hx hy
  | s8 =>
    apply fix
    apply Subtype.ext
    simpa only [val_mul, val_inv, atlas1600ParrottAssignment_val, permutation] using
      Atlas1600SylowTwoCertificate.conjugate_8_4

private theorem sylow_normalizes : ExceptionalParabolics.S ≤ normalizer rootCoset := by
  rw [ExceptionalParabolics.S, atlas1600SylowTwoSubgroup_eq]
  apply (closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact generator_coset _ (by decide) (by decide)

theorem sylow_conjugate_short (g : Atlas1600Group) (hg : g ∈ ExceptionalParabolics.S) :
    ∃ k : Fin 4, g*z*g⁻¹ = shortOrbit k := by
  have hz : z ∈ rootCoset := by change z*z⁻¹ ∈ E; simp
  have hc := (sylow_normalizes hg z).mp hz
  change g*z*g⁻¹*z⁻¹ ∈ E at hc
  rcases mem_secondCenter_iff.mp hc with h | h | h | h
  · refine ⟨0, ?_⟩
    simpa [shortOrbit, orbitConjugator] using mul_inv_eq_iff_eq_mul.mp h
  · exact ⟨1, (mul_inv_eq_iff_eq_mul.mp h).trans orbit_one.symm⟩
  · exact ⟨3, (mul_inv_eq_iff_eq_mul.mp h).trans orbit_three.symm⟩
  · exact ⟨2, (mul_inv_eq_iff_eq_mul.mp h).trans orbit_two.symm⟩
end Tits.InvolutionRootGeometry.ParabolicContainment
