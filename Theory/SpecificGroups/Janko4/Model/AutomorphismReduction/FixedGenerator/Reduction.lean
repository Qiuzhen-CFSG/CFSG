module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction

/-!
# Ambient matrix implementation of automorphisms fixing the J₄ generator

This conditional reduction separates two concrete matrix questions. An
invertible matrix implementing an automorphism on the two certified generators
implements it on the whole carrier and normalizes `matrixGroup`. If it commutes
with the first generator and its square belongs to `matrixGroup`, that square
is an actual model element implementing the square of the automorphism.

The two unproved inputs are existence of such ambient implementers and square
membership for the ambient normalizer elements centralizing the first generator.
They may be established independently. Neither is asserted by this module, and
an ambient unit is never treated as a model element without a membership proof.

Source motivation: GLS3, Table 5.3i, states the stronger Out(J₄) = 1; the
quasithin inspection uses its two-group consequence on printed p.510.
The matrix carrier is the ATLAS representation `J4G1-f2r112B0` certified in
`GeneratorCertificates`. The subgroup `max1Subgroup` is not identified with
the centralizer of the first generator here.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator

/-- An automorphism fixing `a` is implemented on `b` by an ambient matrix
unit centralizing the literal matrix of `a`. This does not assert membership
of that unit in the model. -/
def AmbientImplementation : Prop :=
  ∀ α : MulAut Model, α a = a →
    ∃ u : BinaryMatrixˣ, u * matrixUnitA = matrixUnitA * u ∧
      toAmbient (α b) = u * matrixUnitB * u⁻¹

/-- The required square-membership calculation in the actual ambient matrix
group. The normalizer and centralizing condition are independent of any
chosen automorphism or implementer. -/
def CentralizingNormalizerSquares : Prop :=
  ∀ u : BinaryMatrixˣ, u ∈ Subgroup.normalizer (matrixGroup : Set BinaryMatrixˣ) →
    u * matrixUnitA = matrixUnitA * u → u ^ 2 ∈ matrixGroup

/-- Equality of the two generator images extends to the whole representation. -/
theorem ambient_conj_of_generator_images (α : MulAut Model) (u : BinaryMatrixˣ)
    (ha : toAmbient (α a) = u * matrixUnitA * u⁻¹)
    (hb : toAmbient (α b) = u * matrixUnitB * u⁻¹) (x : Model) :
    toAmbient (α x) = u * toAmbient x * u⁻¹ := by
  have h : toAmbient.comp α.toMonoidHom =
      (MulAut.conj u).toMonoidHom.comp toAmbient := by
    apply MonoidHom.eq_of_eqOn_dense closure_a_b
    intro y hy
    rcases hy with rfl | hy
    · exact ha
    · exact Set.mem_singleton_iff.mp hy ▸ hb
  exact DFunLike.congr_fun h x

/-- A simultaneous implementer of the two generator images normalizes the
actual matrix subgroup. Surjectivity of the automorphism gives the reverse
containment, without an order calculation. -/
theorem ambient_normalizer_of_generator_images (α : MulAut Model) (u : BinaryMatrixˣ)
    (ha : toAmbient (α a) = u * matrixUnitA * u⁻¹)
    (hb : toAmbient (α b) = u * matrixUnitB * u⁻¹) :
    u ∈ Subgroup.normalizer (matrixGroup : Set BinaryMatrixˣ) := by
  have h := ambient_conj_of_generator_images α u ha hb
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    let x : Model := ⟨y, hy⟩
    have hx := (α x).property
    change toAmbient (α x) ∈ matrixGroup at hx
    rwa [h x] at hx
  · intro hy
    let x : Model := ⟨u * y * u⁻¹, hy⟩
    have hx := (α.symm x).property
    change toAmbient (α.symm x) ∈ matrixGroup at hx
    have he : toAmbient (α.symm x) = y := by
      have h' := h (α.symm x)
      rw [α.apply_symm_apply] at h'
      change u * y * u⁻¹ = u * toAmbient (α.symm x) * u⁻¹ at h'
      exact (mul_left_cancel (mul_right_cancel h')).symm
    rwa [he] at hx

/-- Square membership supplies the conjugator in `Model`, with centralization
of `a` retained. No ambient conjugator is substituted for a model element. -/
theorem square_inner_of_ambient_implementation
    (α : MulAut Model) (ha : α a = a) (u : BinaryMatrixˣ)
    (hua : u * matrixUnitA = matrixUnitA * u)
    (hub : toAmbient (α b) = u * matrixUnitB * u⁻¹)
    (hu2 : u ^ 2 ∈ matrixGroup) :
    ∃ c : Model, c * a = a * c ∧ α ^ 2 = MulAut.conj c := by
  have hαa : toAmbient (α a) = u * matrixUnitA * u⁻¹ := by
    rw [ha, toAmbient_a, hua, mul_inv_cancel_right]
  have h := ambient_conj_of_generator_images α u hαa hub
  let c : Model := ⟨u ^ 2, hu2⟩
  have hc : toAmbient c = u ^ 2 := rfl
  refine ⟨c, ?_, ?_⟩
  · apply toAmbient_injective
    rw [map_mul, map_mul, hc, toAmbient_a]
    calc
      u ^ 2 * matrixUnitA = u * (u * matrixUnitA) := by rw [pow_two, mul_assoc]
      _ = u * (matrixUnitA * u) := by rw [hua]
      _ = (matrixUnitA * u) * u := by rw [← mul_assoc, hua]
      _ = matrixUnitA * u ^ 2 := by rw [pow_two, mul_assoc]
  · apply MulEquiv.ext
    intro x
    apply toAmbient_injective
    change toAmbient (α (α x)) = toAmbient (c * x * c⁻¹)
    rw [h, h, map_mul, map_mul, map_inv, hc]
    simp only [pow_two, mul_inv_rev, mul_assoc]

end Janko4.OuterReduction.FixedGenerator

namespace Janko4.OuterReduction

/-- The two independent matrix inputs imply the required generator orbit.
The unconditional theorem must still establish both inputs. -/
theorem fixedGeneratorSquareOrbit_of_ambient
    (himpl : FixedGenerator.AmbientImplementation)
    (hnorm : FixedGenerator.CentralizingNormalizerSquares) :
    FixedGeneratorSquareOrbit := by
  intro α ha
  obtain ⟨u, hua, hub⟩ := himpl α ha
  have hαa : toAmbient (α a) = u * matrixUnitA * u⁻¹ := by
    rw [ha, toAmbient_a, hua, mul_inv_cancel_right]
  have hun := FixedGenerator.ambient_normalizer_of_generator_images α u hαa hub
  obtain ⟨c, hca, hc⟩ := FixedGenerator.square_inner_of_ambient_implementation
    α ha u hua hub (hnorm u hun hua)
  exact ⟨c, hca, DFunLike.congr_fun hc b⟩

end Janko4.OuterReduction
