module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Graph.Model

/-!
# Reduction of the full graph centralizer to orthogonal matrices

Every coefficient automorphism of GF(4) is identity or Frobenius. Full
standard coverage therefore writes a graph-centralizing automorphism as
a graph-centralizing linear factor, a field factor and a graph factor.
If the linear factor can be normalized to an orthogonal determinant-one
matrix, the faithful candidate map is surjective.

The linear normalization remains an explicit matrix hypothesis. No
full-centralizer calculation or Sylow model is asserted unconditionally
here. Source: Aschbacher–Smith 16.1.4(6), printed p.1171, and the
quaternion placement in the proof on printed p.1192.
-/

public section
noncomputable section
open Subgroup
open Matrix.PSL3.OuterSolvable
open Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer
namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Graph

private theorem coefficient_eq_one_or_frobenius (σ : F ≃+* F) :
    σ = 1 ∨ σ = fieldFrobenius := by
  classical
  have hs : fieldFrobenius ^ 2 = 1 := by
    ext x
    exact fieldFrobenius_involutive x
  have hn : fieldFrobenius ≠ 1 := by
    intro he
    obtain ⟨x, hx⟩ := exists_fieldFrobenius_ne
    exact hx (congrArg (fun τ : F ≃+* F => τ x) he)
  have ho : orderOf fieldFrobenius = 2 := orderOf_eq_prime hs hn
  have hm : σ ∈ zpowers fieldFrobenius := by
    rw [← PSL3.FieldComponentFixer.coefficient_fixer_eq_zpowers]
    intro x
    rcases eq_zero_or_one_of_sq_eq_self x.property with hx | hx
    · change σ x.val = x.val
      rw [hx, map_zero]
    · change σ x.val = x.val
      rw [hx, map_one]
  have hf : IsOfFinOrder fieldFrobenius :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hs⟩
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (hf.mem_zpowers_iff_mem_range_orderOf.mp hm)
  have hn' : n < 2 := by simpa only [Finset.mem_range, ho] using hn
  interval_cases n
  · exact Or.inl (by simpa only [pow_zero] using he.symm)
  · exact Or.inr (by simpa only [pow_one] using he.symm)

/-- Every coefficient action over GF(4) is one of the two marked field actions. -/
theorem exists_fieldParameter (σ : F ≃+* F) :
    ∃ s : C2, PSL3.OuterSolvable.fieldAction F σ = Matrix.PSL3Four.fieldAction s := by
  rcases coefficient_eq_one_or_frobenius σ with rfl | rfl
  · exact ⟨1, by rw [map_one, map_one]⟩
  · exact ⟨Multiplicative.ofAdd (1 : ZMod 2), by
      rw [fieldAction_generator, frobenius_eq_fieldAction]⟩

/-- Full coverage reduces the centralizer calculation to its linear factor. -/
theorem exists_centralizing_linear_form
    (a : automorphismCentralizer (graph F)) :
    ∃ (A : GeneralLinearGroup (Fin 3) F) (s t : C2),
      Commute (linearConj F A) (graph F) ∧
      a.val = linearConj F A * Matrix.PSL3Four.fieldAction s *
        involutionHom (graph F) (graph_sq F) t := by
  obtain ⟨A, σ, t, ha⟩ := QuaternionPlacement.exists_standardForm a.val
  obtain ⟨s, hs⟩ := exists_fieldParameter σ
  have he : a.val = linearConj F A * Matrix.PSL3Four.fieldAction s *
      involutionHom (graph F) (graph_sq F) t := by
    simpa only [standardForm, hs] using ha
  have hc : Commute a.val (graph F) := mem_centralizer_singleton_iff.mp a.property
  have ht : Commute (Matrix.PSL3Four.fieldAction s *
      involutionHom (graph F) (graph_sq F) t) (graph F) :=
    (fieldAction_commute_graph s).mul_left ((Commute.refl (graph F)).pow_left t.toAdd.val)
  refine ⟨A, s, t, ?_, he⟩
  have h := hc.mul_left ht.inv_left
  have hh : a.val * (Matrix.PSL3Four.fieldAction s *
      involutionHom (graph F) (graph_sq F) t)⁻¹ = linearConj F A := by
    rw [he]
    group
  rwa [hh] at h

/-- Orthogonal normalization of the linear factor suffices for full surjectivity. -/
theorem centralizerHom_surjective_of_linear_normalization
    (hlinear : ∀ A : GeneralLinearGroup (Fin 3) F,
      Commute (linearConj F A) (graph F) → ∃ x : Fixed, linearConj F A = inner x) :
    Function.Surjective centralizerHom := by
  intro a
  obtain ⟨A, s, t, hc, he⟩ := exists_centralizing_linear_form a
  obtain ⟨x, hx⟩ := hlinear A hc
  refine ⟨(⟨x, s⟩, t), Subtype.ext ?_⟩
  change inner x * Matrix.PSL3Four.fieldAction s *
    involutionHom (graph F) (graph_sq F) t = a.val
  rw [← hx, ← he]

/-- A genuine centralizer equivalence once the matrix normalization is supplied. -/
def centralizerEquiv_of_linear_normalization
    (hlinear : ∀ A : GeneralLinearGroup (Fin 3) F,
      Commute (linearConj F A) (graph F) → ∃ x : Fixed, linearConj F A = inner x) :
    Model ≃* automorphismCentralizer (graph F) :=
  MulEquiv.ofBijective centralizerHom ⟨centralizerHom_injective,
    centralizerHom_surjective_of_linear_normalization hlinear⟩

end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Graph
