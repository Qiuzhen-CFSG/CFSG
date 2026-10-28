module

public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightCoordinates
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Geometry
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Weight-four geometry in the eight-point binary permutation module

The half-weight form on the actual six-dimensional natural quotient is
singular precisely on classes of weight zero, four or eight. Only the
weight-four classes are nonzero. Its nondegenerate polar form bounds totally
singular subspaces by dimension three. A core subspace whose nonzero words
all have weight four excludes the constant line, so projection preserves
its dimension and gives the same bound in the seven-dimensional core.

The quadratic form and its equivariant split-six-space identification are
reused from `TerminalOrthogonal.EightCoordinates`, which preserves the
attribution of the ATLAS half-weight construction. The proofs here use
weight arithmetic and nondegenerate bilinear algebra, without enumerating
subspaces or changing the permutation actions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §12.6, especially 12.6.1 and 12.6.20, printed
pp.823 and 828–829 (PDF pp.840 and 845–846).
-/

public section

open Module
namespace BinaryPermutation.EightGeometry
open TerminalOrthogonal.Eight

/-- The half-weight form uses the original core-to-natural quotient map. -/
theorem form_coreToNatural (v : core (Fin 8)) :
    form (coreToNatural (Fin 8) v) =
      Atlas.Order20160A8.HalfWeight.binaryHalfWeight v.val := by
  rw [show coreToNatural (Fin 8) v = naturalEquiv (Submodule.Quotient.mk v) from
      Subtype.ext (naturalEquiv_mk v).symm,
    form_naturalEquiv]
  rfl

/-- The kernel consists precisely of zero and the constant all-one word. -/
theorem coreToNatural_eq_zero (v : core (Fin 8)) :
    coreToNatural (Fin 8) v = 0 ↔ v.val = 0 ∨ v.val = allOne (Fin 8) := by
  rw [Subtype.ext_iff]
  change (constants (Fin 8)).mkQ v.val = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    constants, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have hbits : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    have hc' := hbits c
    rcases hc' with rfl | rfl
    · left; simpa using hc.symm
    · right; simpa using hc.symm
  · rintro (h | h)
    · exact ⟨0, by simpa using h.symm⟩
    · exact ⟨1, by simpa using h.symm⟩

private theorem weight_eight_iff (v : Full (Fin 8)) :
    hammingNorm v = 8 ↔ v = allOne (Fin 8) := by
  change (Finset.univ.filter (fun i => v i ≠ 0)).card =
    (Finset.univ : Finset (Fin 8)).card ↔ _
  rw [Finset.card_filter_eq_iff]
  simp only [Finset.mem_univ, forall_true_left]
  constructor
  · intro h
    funext i
    have hc : v i = 0 ∨ v i = 1 := by
      have hbit : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      exact hbit _
    exact hc.resolve_left (h i)
  · rintro rfl i
    exact one_ne_zero

private theorem core_weights (v : core (Fin 8)) :
    hammingNorm v.val = 0 ∨ hammingNorm v.val = 2 ∨ hammingNorm v.val = 4 ∨
      hammingNorm v.val = 6 ∨ hammingNorm v.val = 8 := by
  have hbound : hammingNorm v.val ≤ 8 := hammingNorm_le_card_fintype
  have heven : 2 ∣ hammingNorm v.val := Atlas.Order20160A8.DeletedEight.even_weight v
  omega

/-- Singularity on a representative includes the two words in the constant line. -/
theorem singular_core_iff (v : core (Fin 8)) :
    form (coreToNatural (Fin 8) v) = 0 ↔
      v.val = 0 ∨ v.val = allOne (Fin 8) ∨ hammingNorm v.val = 4 := by
  rw [← hammingNorm_eq_zero, ← weight_eight_iff, form_coreToNatural]
  change ((hammingNorm v.val / 2 : ℕ) : ZMod 2) = 0 ↔ _
  rcases core_weights v with h | h | h | h | h <;> rw [h] <;> decide

/-- Nonsingular classes have representatives of weight two or six. -/
theorem nonsingular_core_iff (v : core (Fin 8)) :
    form (coreToNatural (Fin 8) v) = 1 ↔
      hammingNorm v.val = 2 ∨ hammingNorm v.val = 6 := by
  rw [form_coreToNatural]
  change ((hammingNorm v.val / 2 : ℕ) : ZMod 2) = 1 ↔ _
  rcases core_weights v with h | h | h | h | h <;> rw [h] <;> decide

/-- A nonzero singular class is represented precisely by a weight-four core word. -/
theorem nonzero_singular_core_iff (v : core (Fin 8)) :
    coreToNatural (Fin 8) v ≠ 0 ∧ form (coreToNatural (Fin 8) v) = 0 ↔
      hammingNorm v.val = 4 := by
  rw [ne_eq, coreToNatural_eq_zero, singular_core_iff, ← weight_eight_iff,
    ← hammingNorm_eq_zero]
  omega

/-- Every nonzero singular natural vector has a weight-four representative. -/
theorem singular_iff_weight_four (v : natural (Fin 8)) (hv : v ≠ 0) :
    form v = 0 ↔ ∃ w : core (Fin 8), coreToNatural (Fin 8) w = v ∧ hammingNorm w.val = 4 := by
  obtain ⟨w, rfl⟩ := coreToNatural_surjective v
  constructor
  · intro h
    exact ⟨w, rfl, (nonzero_singular_core_iff w).mp ⟨hv, h⟩⟩
  · rintro ⟨u, hu, hw⟩
    rw [← hu]
    exact ((nonzero_singular_core_iff u).mpr hw).2

/-- The polar form is nondegenerate in characteristic two. -/
theorem polar_nondegenerate : form.polarBilin.Nondegenerate := by
  have hp (x y : ClassicalOrthogonal.VectorD 3 (ZMod 2)) :
      form.polarBilin (splitIsometry x) (splitIsometry y) =
        (ClassicalOrthogonal.formD 3 (ZMod 2)).polarBilin x y := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      ← map_add, splitIsometry.map_app]
  have hs (v : natural (Fin 8)) (hv : ∀ w, form.polarBilin v w = 0) : v = 0 := by
    obtain ⟨x, rfl⟩ := splitIsometry.surjective v
    have hx : x = 0 := ClassicalOrthogonal.polarD_separating x (fun y => by
      rw [← hp]
      exact hv _)
    rw [hx, map_zero]
  exact ⟨hs, fun v hv => hs v (fun w => by
    simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using hv w)⟩

/-- A totally singular subspace of the natural six-space has dimension at most three. -/
theorem finrank_singular_le (W : Submodule (ZMod 2) (natural (Fin 8)))
    (hW : ∀ v ∈ W, form v = 0) : finrank (ZMod 2) W ≤ 3 := by
  have hle : W ≤ LinearMap.BilinForm.orthogonal form.polarBilin W := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    change form (u + v) - form u - form v = 0
    rw [hW _ (W.add_mem hu hv), hW _ hu, hW _ hv]
    simp
  have hdim := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal polar_nondegenerate, finrank_natural] at hdim
  omega

/-- A core subspace containing only zero and weight-four words projects
injectively to the natural section: it does not contain the constant word. -/
theorem coreToNatural_injective_on_weight_four
    (U : Submodule (ZMod 2) (core (Fin 8)))
    (hU : ∀ v ∈ U, v ≠ 0 → hammingNorm v.val = 4) :
    Function.Injective ((coreToNatural (Fin 8)).domRestrict U) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro v hv
  change coreToNatural (Fin 8) v.val = 0 at hv
  rcases (coreToNatural_eq_zero v.val).mp hv with h0 | h1
  · exact Subtype.ext (Subtype.ext h0)
  · by_contra hn
    have hn' : v.val ≠ 0 := fun h => hn (Subtype.ext h)
    have hw := hU v.val v.property hn'
    rw [h1] at hw
    have hone : hammingNorm (allOne (Fin 8)) = 8 := by decide
    omega

/-- The constant line is excluded explicitly; consequently the bound for a
constant-weight-four core subspace is three, not four. -/
theorem finrank_weight_four_le
    (U : Submodule (ZMod 2) (core (Fin 8)))
    (hU : ∀ v ∈ U, v ≠ 0 → hammingNorm v.val = 4) :
    finrank (ZMod 2) U ≤ 3 := by
  let f := (coreToNatural (Fin 8)).domRestrict U
  have hf : Function.Injective f := coreToNatural_injective_on_weight_four U hU
  rw [← LinearMap.finrank_range_of_inj hf]
  apply finrank_singular_le
  rintro _ ⟨v, rfl⟩
  change form (coreToNatural (Fin 8) v.val) = 0
  by_cases hv : v.val = 0
  · simp [hv]
  · exact ((nonzero_singular_core_iff v.val).mpr (hU v.val v.property hv)).2

/-- The corresponding bound in the natural quotient uses singularity rather
than a choice of representative. Zero is exempted from the weight condition. -/
theorem finrank_nonzero_singular_le
    (U : Submodule (ZMod 2) (natural (Fin 8)))
    (hU : ∀ v ∈ U, v ≠ 0 → form v = 0) :
    finrank (ZMod 2) U ≤ 3 := by
  apply finrank_singular_le
  intro v hv
  by_cases h0 : v = 0
  · simp [h0]
  · exact hU v hv h0

end BinaryPermutation.EightGeometry
