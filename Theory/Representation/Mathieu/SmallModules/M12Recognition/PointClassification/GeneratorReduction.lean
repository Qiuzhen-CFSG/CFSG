module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizerReduction

/-!
# From normalizer scalars to full M₁₁ intertwiners

The standard involution A and the selected eleven-element C = AB generate
M₁₁. Thus an automorphism of the reference C₁₁:C₅ module which intertwines
the matrix of A also intertwines the entire M₁₁ action, provided the actions
already agree on the literal normalizer. The proof uses the actual subgroup
inclusion and the marked ATLAS generators.

This isolates the remaining matrix rigidity problem; it does not construct
the correcting normalizer-module automorphism.

Source application: the James classification input to Aschbacher--Smith,
G.7.3(2), printed p.348 (PDF p.359). Generation is proved in
`Theory.Mathieu.M11.Properties.Order`.
-/

public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification
open Sporadic.Mathieu

/-- The standard involution and the selected eleven-element generate M₁₁. -/
theorem involution_eleven_closure :
    Subgroup.closure ({m11GeneratorAInM11, m11Sylow11Generator} : Set M11) = ⊤ := by
  apply top_unique
  rw [← m11_generators_closure_eq_top]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | rfl
  · exact Subgroup.subset_closure (by simp)
  · have ha : m11GeneratorAInM11 ∈
        Subgroup.closure ({m11GeneratorAInM11, m11Sylow11Generator} : Set M11) :=
      Subgroup.subset_closure (by simp)
    have hc : m11Sylow11Generator ∈
        Subgroup.closure ({m11GeneratorAInM11, m11Sylow11Generator} : Set M11) :=
      Subgroup.subset_closure (by simp)
    have hab : m11GeneratorAInM11⁻¹ * m11Sylow11Generator = m11GeneratorBInM11 := by
      simp only [m11Sylow11Generator, inv_mul_cancel_left]
    have h := (Subgroup.closure ({m11GeneratorAInM11, m11Sylow11Generator} : Set M11)).mul_mem
      ((Subgroup.closure _).inv_mem ha) hc
    rwa [hab] at h

/-- The selected eleven-element belongs to its literal normalizer. -/
theorem eleven_mem_normalizer : m11Sylow11Generator ∈ m11Sylow11Normalizer := by
  exact Subgroup.le_normalizer m11Sylow11Generator_mem_subgroup

/-- In normalizer coordinates, only the standard involution still needs to be intertwined. -/
noncomputable def equivOfNormalizerAndInvolution
    (τ : Representation (ZMod 2) M11 M12Heart)
    (hon : ∀ g : m11Sylow11Normalizer, τ g.val = pointRepresentation g.val)
    (e : normalizerRepresentation.Equiv normalizerRepresentation)
    (ha : e.toLinearMap.comp (τ m11GeneratorAInM11) =
      (pointRepresentation m11GeneratorAInM11).comp e.toLinearMap) :
    τ.Equiv pointRepresentation := by
  let τ' := normalizerCoordinateRepresentation τ e.toLinearEquiv
  have hn (g : m11Sylow11Normalizer) : τ' g.val = pointRepresentation g.val := by
    change e.toLinearEquiv.conj (τ g.val) = pointRepresentation g.val
    rw [hon g]
    exact e.conj_apply_self g
  have hA : τ' m11GeneratorAInM11 = pointRepresentation m11GeneratorAInM11 := by
    apply LinearMap.ext
    intro v
    change e (τ m11GeneratorAInM11 (e.symm v)) = pointRepresentation m11GeneratorAInM11 v
    have h := LinearMap.congr_fun ha (e.symm v)
    change e (τ m11GeneratorAInM11 (e.symm v)) =
      pointRepresentation m11GeneratorAInM11 (e (e.symm v)) at h
    simpa only [Representation.Equiv.apply_symm_apply] using h
  have ht : τ' = pointRepresentation := by
    apply MonoidHom.eq_of_eqOn_dense involution_eleven_closure
    intro g hg
    rcases hg with rfl | rfl
    · exact hA
    · exact hn ⟨m11Sylow11Generator, eleven_mem_normalizer⟩
  have E := normalizerCoordinateEquiv τ e.toLinearEquiv
  change τ.Equiv τ' at E
  rw [ht] at E
  exact E

end Representation.MathieuSmall.M12Recognition.PointClassification
