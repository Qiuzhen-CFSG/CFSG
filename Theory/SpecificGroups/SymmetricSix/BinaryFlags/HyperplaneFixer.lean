module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
public import Mathlib.GroupTheory.Perm.Sign

/-!
# The transposition fixing a natural hyperplane

Three fixed duad classes force a permutation to fix the first four letters,
so the canonical perpendicular hyperplane has pointwise fixer of order two.
The actual alternating action transports this calculation to every line of
its four-dimensional natural module. No transvection classification or
subgroup enumeration is assumed.

Source: Aschbacher–Smith, 13.7.3(4),(7), printed p.936.
-/

@[expose] public section
open BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.HyperplaneFixer
open NaturalGeometry NaturalPairing

private def corePair (i j : Fin 6) : core (Fin 6) :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core, Finset.sum_add_distrib]; decide⟩

private theorem orth01 : form (pairVector 4 5) (pairVector 0 1) = 0 := by
  change naturalPairing (Fin 6) (coreToNatural (Fin 6) (corePair 4 5))
    (coreToNatural (Fin 6) (corePair 0 1)) = 0
  rw [naturalPairing_apply_core]
  decide
private theorem orth02 : form (pairVector 4 5) (pairVector 0 2) = 0 := by
  change naturalPairing (Fin 6) (coreToNatural (Fin 6) (corePair 4 5))
    (coreToNatural (Fin 6) (corePair 0 2)) = 0
  rw [naturalPairing_apply_core]
  decide
private theorem orth03 : form (pairVector 4 5) (pairVector 0 3) = 0 := by
  change naturalPairing (Fin 6) (coreToNatural (Fin 6) (corePair 4 5))
    (coreToNatural (Fin 6) (corePair 0 3)) = 0
  rw [naturalPairing_apply_core]
  decide

private theorem canonical_fixer (g : Equiv.Perm (Fin 6))
    (hg : ∀ v : natural (Fin 6), form (pairVector 4 5) v = 0 →
      naturalRepresentation (Fin 6) g v = v) :
    g = 1 ∨ g = Equiv.swap 4 5 := by
  have h01 := hg _ orth01
  have h02 := hg _ orth02
  have h03 := hg _ orth03
  rw [pairVector_map, pairVector_eq_iff (g.injective.ne (by decide)) (by decide)] at h01 h02 h03
  have h0 : g 0 = 0 := by
    have h1 : g 0 = 0 ∨ g 0 = 1 := by
      have hm : g 0 ∈ ({g 0, g 1} : Finset (Fin 6)) := by simp
      rw [show ({g 0, g 1} : Finset (Fin 6)) = {0,1} from h01] at hm
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    have h2 : g 0 = 0 ∨ g 0 = 2 := by
      have hm : g 0 ∈ ({g 0, g 2} : Finset (Fin 6)) := by simp
      rw [show ({g 0, g 2} : Finset (Fin 6)) = {0,2} from h02] at hm
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    omega
  have hfix {i : Fin 6} (hi : i ≠ 0)
      (hh : ({g 0, g i} : Finset (Fin 6)) = {0,i}) : g i = i := by
    have hm : g i ∈ ({g 0, g i} : Finset (Fin 6)) := by simp
    rw [hh] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm.resolve_left (by intro he; exact hi (g.injective (he.trans h0.symm)))
  have h1 := hfix (by decide : (1 : Fin 6) ≠ 0) h01
  have h2 := hfix (by decide : (2 : Fin 6) ≠ 0) h02
  have h3 := hfix (by decide : (3 : Fin 6) ≠ 0) h03
  have h4 : g 4 = 4 ∨ g 4 = 5 := by
    have hn0 := g.injective.ne (show (4 : Fin 6) ≠ 0 by decide)
    have hn1 := g.injective.ne (show (4 : Fin 6) ≠ 1 by decide)
    have hn2 := g.injective.ne (show (4 : Fin 6) ≠ 2 by decide)
    have hn3 := g.injective.ne (show (4 : Fin 6) ≠ 3 by decide)
    rw [h0] at hn0
    rw [h1] at hn1
    rw [h2] at hn2
    rw [h3] at hn3
    omega
  have h5 : g 5 = 4 ∨ g 5 = 5 := by
    have hn0 := g.injective.ne (show (5 : Fin 6) ≠ 0 by decide)
    have hn1 := g.injective.ne (show (5 : Fin 6) ≠ 1 by decide)
    have hn2 := g.injective.ne (show (5 : Fin 6) ≠ 2 by decide)
    have hn3 := g.injective.ne (show (5 : Fin 6) ≠ 3 by decide)
    rw [h0] at hn0
    rw [h1] at hn1
    rw [h2] at hn2
    rw [h3] at hn3
    omega
  rcases h4 with h4 | h4
  · have h5 : g 5 = 5 := h5.resolve_left (by intro h; have := g.injective (h.trans h4.symm); contradiction)
    left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · have h5 : g 5 = 4 := h5.resolve_right (by intro h; have := g.injective (h.trans h4.symm); contradiction)
    right
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

/-- The pointwise fixer of a perpendicular hyperplane contains at most the
identity and one genuine transposition. -/
theorem exists_swap_bound (z : natural (Fin 6)) (hz : z ≠ 0) :
    ∃ t : Equiv.Perm (Fin 6), t.IsSwap ∧
      ∀ g : Equiv.Perm (Fin 6),
        (∀ v, form z v = 0 → naturalRepresentation (Fin 6) g v = v) →
        g = 1 ∨ g = t := by
  obtain ⟨a, ha⟩ := NaturalTransport.exists_even_image z hz
  let t := a.val * Equiv.swap 4 5 * a.val⁻¹
  have ht : t.IsSwap := by
    rw [show t = Equiv.swap (a.val 4) (a.val 5) from (Equiv.swap_apply_apply _ _ _).symm]
    exact ⟨a.val 4, a.val 5, a.val.injective.ne (by decide), rfl⟩
  refine ⟨t, ht, fun g hg => ?_⟩
  have hfix : ∀ v, form (pairVector 4 5) v = 0 →
      naturalRepresentation (Fin 6) (a.val⁻¹ * g * a.val) v = v := by
    intro v hv
    have hgv := hg (naturalRepresentation (Fin 6) a.val v) (by
      rw [← ha, form_invariant]
      exact hv)
    have he := congrArg (naturalRepresentation (Fin 6) a.val⁻¹) hgv
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply, mul_assoc] using he
  rcases canonical_fixer _ hfix with he | he
  · left
    have hm := congrArg (fun x => a.val * x * a.val⁻¹) he
    simpa only [mul_assoc, mul_inv_cancel, inv_mul_cancel, mul_inv_cancel_left, one_mul, mul_one] using hm
  · right
    have hm := congrArg (fun x => a.val * x * a.val⁻¹) he
    simpa only [mul_assoc, mul_inv_cancel, inv_mul_cancel, mul_inv_cancel_left, one_mul, mul_one, t] using hm

/-- The bound expressed on an arbitrary marked line. -/
theorem exists_swap_bound_line (P : Submodule (ZMod 2) (natural (Fin 6)))
    (hP : Module.finrank (ZMod 2) P = 1) :
    ∃ t : Equiv.Perm (Fin 6), t.IsSwap ∧
      ∀ g : Equiv.Perm (Fin 6),
        (∀ v ∈ form.orthogonal P, naturalRepresentation (Fin 6) g v = v) →
        g = 1 ∨ g = t := by
  have hn : P ≠ ⊥ := by
    intro he
    rw [he] at hP
    have hz : Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) (natural (Fin 6))) = 0 := by
      exact Module.finrank_zero_of_subsingleton
    omega
  obtain ⟨z, hzP, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  obtain ⟨t, ht, htf⟩ := exists_swap_bound z hz
  refine ⟨t, ht, fun g hg => htf g fun v hv => hg v ?_⟩
  intro w hw
  have hzn : (⟨z, hzP⟩ : P) ≠ 0 := fun he => hz (congrArg Subtype.val he)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨z, hzP⟩ : P) hzn).mp hP ⟨w,hw⟩
  have he : c • z = w := congrArg Subtype.val hc
  rw [← he, LinearMap.BilinForm.smul_left, hv, mul_zero]

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.HyperplaneFixer
