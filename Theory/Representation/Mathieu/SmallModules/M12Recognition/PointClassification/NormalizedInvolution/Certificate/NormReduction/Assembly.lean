module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.Data

/-!
# From finite norm relations to the actual quotient

The 600 basis-column relations extend by linearity to the whole coordinate
space. The empty basis word and generation of the finite group by A and B
then imply that every group-algebra element lifts modulo the literal
two-sided ideal `elevenIdeal`. These implications keep the finite relations
explicit; no quotient certificate is asserted in this module.

Source application: the finite algebra input to the James reduction in
Aschbacher–Smith G.7.3(2), printed p.348/PDF p.359.
-/

@[expose] public section
open scoped BigOperators MonoidAlgebra
open Sporadic.Mathieu
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
namespace NormReduction
open CertificateData

abbrev R := (ZMod 2)[M11]

/-- The finite relations still to be checked in the literal norm ideal. -/
def ColumnRelations : Prop := ∀ (s : Fin 2) (j : Fin 300),
  MonoidAlgebra.single (generator s) 1 * basisElement j -
    lift (action s (Pi.single j 1)) ∈ elevenIdeal

theorem lift_apply (v : Space) : lift v = ∑ i, v i • basisElement i := by
  simp [lift, LinearMap.sum_apply]

theorem lift_single (j : Fin 300) : lift (Pi.single j 1) = basisElement j := by
  rw [lift_apply]
  simp [Pi.single_apply]

theorem smul_mem_elevenIdeal (c : ZMod 2) {x : R} (hx : x ∈ elevenIdeal) :
    c • x ∈ elevenIdeal := by
  rw [Algebra.smul_def]
  exact elevenIdeal.mul_mem_left _ _ hx

private theorem linear_mem_of_single (f : Space →ₗ[ZMod 2] R)
    (h : ∀ j, f (Pi.single j 1) ∈ elevenIdeal) (v : Space) : f v ∈ elevenIdeal := by
  rw [pi_eq_sum_univ' v, map_sum]
  apply sum_mem
  intro j _
  rw [map_smul]
  exact smul_mem_elevenIdeal _ (h j)

private theorem linear_relation_of_single (a : R) (L : Space →ₗ[ZMod 2] R)
    (A : Module.End (ZMod 2) Space)
    (h : ∀ j, a * L (Pi.single j 1) - L (A (Pi.single j 1)) ∈ elevenIdeal)
    (v : Space) : a * L v - L (A v) ∈ elevenIdeal := by
  let f := (LinearMap.mulLeft (ZMod 2) a).comp L - L.comp A
  have hf (j : Fin 300) : f (Pi.single j 1) ∈ elevenIdeal := h j
  exact linear_mem_of_single f hf v

/-- The column relations imply compatibility for every coordinate vector. -/
theorem generator_lift_sub_mem_of_columns (h : ColumnRelations)
    (s : Fin 2) (v : Space) :
    MonoidAlgebra.single (generator s) 1 * lift v - lift (action s v) ∈ elevenIdeal := by
  apply linear_relation_of_single
  intro j
  rw [lift_single]
  exact h s j

private theorem generators_monoid_closure :
    Submonoid.closure (Set.range generator) = ⊤ := by
  have hr : Set.range generator = {m11GeneratorAInM11, m11GeneratorBInM11} := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      fin_cases s <;> simp [generator]
    · intro hg
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · exact ⟨0, by simp [generator]⟩
      · obtain rfl := Set.mem_singleton_iff.mp hg
        exact ⟨1, by simp [generator]⟩
  rw [hr, ← Subgroup.closure_toSubmonoid_of_finite, m11_generators_closure_eq_top]
  rfl

private theorem basisElement_zero : basisElement 0 = 1 := by
  rw [basisElement, show basisWord 0 = [] from by decide +kernel]
  simp [CertificateData.evalWord, MonoidAlgebra.one_def]

private theorem single_has_lift (h : ColumnRelations) (g : M11) :
    ∃ v : Space, MonoidAlgebra.single g 1 - lift v ∈ elevenIdeal := by
  apply Submonoid.induction_of_closure_eq_top_left
    (motive := fun g => ∃ v : Space, MonoidAlgebra.single g 1 - lift v ∈ elevenIdeal)
    generators_monoid_closure g
  · refine ⟨Pi.single 0 1, ?_⟩
    rw [lift_single, basisElement_zero]
    rw [← MonoidAlgebra.one_def, sub_self]
    exact elevenIdeal.zero_mem
  · rintro _ ⟨s, rfl⟩ y ⟨v, hv⟩
    refine ⟨action s v, ?_⟩
    have h₁ := elevenIdeal.mul_mem_left (MonoidAlgebra.single (generator s) 1) _ hv
    have h₂ := generator_lift_sub_mem_of_columns h s v
    have he : MonoidAlgebra.single (generator s * y) 1 - lift (action s v) =
        MonoidAlgebra.single (generator s) 1 *
          (MonoidAlgebra.single y 1 - lift v) +
        (MonoidAlgebra.single (generator s) 1 * lift v - lift (action s v)) := by
      rw [mul_sub, MonoidAlgebra.single_mul_single, one_mul]
      abel
    rw [he]
    exact elevenIdeal.add_mem h₁ h₂

/-- The empty basis word and A/B generation turn the finite relations into
surjectivity onto the actual two-sided norm quotient. -/
theorem exists_lift_of_columns (h : ColumnRelations) (x : R) :
    ∃ v : Space, x - lift v ∈ elevenIdeal := by
  induction x using MonoidAlgebra.induction_on with
  | of g => exact single_has_lift h g
  | add x y hx hy =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨w, hw⟩ := hy
    refine ⟨v + w, ?_⟩
    rw [map_add, show x + y - (lift v + lift w) = (x - lift v) + (y - lift w) by abel]
    exact elevenIdeal.add_mem hv hw
  | smul c x hx =>
    obtain ⟨v, hv⟩ := hx
    refine ⟨c • v, ?_⟩
    rw [map_smul, ← smul_sub]
    exact smul_mem_elevenIdeal c hv

/-- Norm translates are legitimate seeds because the ideal is two-sided. -/
theorem norm_translate_mem (a b : M11) :
    MonoidAlgebra.single a 1 * elevenNorm * MonoidAlgebra.single b 1 ∈ elevenIdeal := by
  apply elevenIdeal.mul_mem_right
  apply elevenIdeal.mul_mem_left
  exact TwoSidedIdeal.subset_span (by simp)

end NormReduction
end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
