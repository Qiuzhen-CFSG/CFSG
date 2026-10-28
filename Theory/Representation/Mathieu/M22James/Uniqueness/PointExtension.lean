module
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointExtension.Words

/-!
# Rigidity of the binary point-stabilizer extension

Agreement on the actual point stabilizer forces equality of the full actions.
For the generator B, compare its unknown matrix with the fixed matrix. The
comparison commutes with the two-point stabilizer and the central scalar.
The small commutant and the relation BHB = HBH force B's matrix to agree.
An explicit double-coset word then determines A. The two certified generators
therefore give the required intertwining linear equivalence, with the original
coordinates and the distinguished central scalar preserved.

This is the extension step for James (1973), Lemma 8.3, used in
Aschbacher–Smith H.12.1(1), printed pp.393–394. Recognition of the restricted
module is not asserted here: agreement on the point stabilizer is an input.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointExtension
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

private def matrixAction (τ : Representation (ZMod 2) M22TripleCover BinarySpace) :
    M22TripleCover →* Matrix12 := Matrix.toLinAlgEquiv'.symm.toMonoidHom.comp τ

private theorem matrixAction_binary (g : M22TripleCover) :
    matrixAction binaryRepresentation g = ((g : Matrix12ˣ) : Matrix12) :=
  Matrix.toLinAlgEquiv'.symm_apply_apply _

private theorem comparison_commutes {G R : Type*} [Group G] [Monoid R]
    (f r : G →* R) (b k : G) (hb : b * b = 1)
    (hk : f k = r k) (hbk : f (b * k * b) = r (b * k * b)) :
    Commute (r b * f b) (r k) := by
  have hf : f b * f b = 1 := by rw [← map_mul, hb, map_one]
  have hr : r b * r b = 1 := by rw [← map_mul, hb, map_one]
  change (r b * f b) * r k = r k * (r b * f b)
  calc
    (r b * f b) * r k = r b * (f b * f k) := by rw [hk, mul_assoc]
    _ = r b * (f b * f k) * (f b * f b) := by rw [hf, mul_one]
    _ = r b * f (b * k * b) * f b := by simp only [map_mul, mul_assoc]
    _ = r b * r (b * k * b) * f b := by rw [hbk]
    _ = r k * (r b * f b) := by
      simp only [map_mul, ← mul_assoc, hr, one_mul]

private theorem scalar_square_conjugate_mem :
    coreGeneratorB * scalar ^ 2 * coreGeneratorB ∈ pointStabilizer := by
  have hs : corePermutationAction scalar = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [corePermutationAction_ker_eq_center]
    exact scalar_mem_center
  have he : corePermutationAction (coreGeneratorB * scalar ^ 2 * coreGeneratorB) = 1 := by
    calc
      _ = corePermutationAction coreGeneratorB * corePermutationAction coreGeneratorB := by
        rw [map_mul, map_mul, map_pow, hs, one_pow, mul_one]
      _ = corePermutationAction (coreGeneratorB * coreGeneratorB) := (map_mul _ _ _).symm
      _ = 1 := (congrArg corePermutationAction generatorB_sq).trans corePermutationAction.map_one
  rw [mem_pointStabilizer, he]
  rfl

private theorem matrix_generatorB_eq
    (τ : Representation (ZMod 2) M22TripleCover BinarySpace)
    (hag : ∀ g : pointStabilizer, τ g = binaryRepresentation g) :
    matrixAction τ coreGeneratorB = matrixB := by
  have hag' (g : M22TripleCover) (hg : g ∈ pointStabilizer) :
      matrixAction τ g = matrixAction binaryRepresentation g :=
    congrArg Matrix.toLinAlgEquiv'.symm (hag ⟨g, hg⟩)
  have hc (g : M22TripleCover) (hg : g ∈ pointStabilizer)
      (hbg : coreGeneratorB * g * coreGeneratorB ∈ pointStabilizer) :
      Commute (matrixB * matrixAction τ coreGeneratorB)
        (matrixAction binaryRepresentation g) := by
    have h := comparison_commutes (matrixAction τ) (matrixAction binaryRepresentation)
      coreGeneratorB g generatorB_sq (hag' g hg) (hag' _ hbg)
    simpa only [matrixAction_binary, show ((coreGeneratorB : Matrix12ˣ) : Matrix12) =
      matrixB from coe_coreB] using h
  apply matrix_extension_rigidity
  · have h := hc wordS wordS_mem conjugate_wordS_mem
    simpa only [matrixAction_binary, coe_wordS] using h
  · have h := hc wordT wordT_mem conjugate_wordT_mem
    simpa only [matrixAction_binary, coe_wordT] using h
  · have h := hc (scalar ^ 2) (pointStabilizer.pow_mem scalar_mem_pointStabilizer 2)
      scalar_square_conjugate_mem
    have hs : matrixAction binaryRepresentation (scalar ^ 2) = matrixJ := by
      rw [matrixAction_binary]
      exact coe_scalarUnit_sq
    exact (congrArg (fun M : Matrix12 =>
      Commute (matrixB * matrixAction τ coreGeneratorB) M) hs).mp h
  · rw [← map_mul, generatorB_sq, map_one]
  · have h := congrArg (matrixAction τ) generatorB_wordH_braid
    have hh : matrixAction τ wordH = matrixH := by
      rw [hag' wordH wordH_mem, matrixAction_binary, coe_wordH]
    simpa only [map_mul, hh] using h

/-- Literal agreement on the actual point stabilizer forces equality of the
whole binary action. No faithfulness or irreducibility premise is needed. -/
theorem eq_of_pointStabilizer_agreement
    (τ : Representation (ZMod 2) M22TripleCover BinarySpace)
    (hag : ∀ g : pointStabilizer, τ g = binaryRepresentation g) :
    τ = binaryRepresentation := by
  have hag' (g : M22TripleCover) (hg : g ∈ pointStabilizer) :
      τ g = binaryRepresentation g := hag ⟨g, hg⟩
  have hb : τ coreGeneratorB = binaryRepresentation coreGeneratorB := by
    apply Matrix.toLinAlgEquiv'.symm.injective
    exact (matrix_generatorB_eq τ hag).trans (by
      change matrixB = matrixAction binaryRepresentation coreGeneratorB
      rw [matrixAction_binary]
      exact coe_coreB.symm)
  have ha : τ coreGeneratorA = binaryRepresentation coreGeneratorA := by
    have he : coreGeneratorA = wordL * coreGeneratorB *
        (coreGeneratorB * wordL⁻¹ * coreGeneratorA) := by
      calc
        coreGeneratorA = wordL * (coreGeneratorB * coreGeneratorB) *
            wordL⁻¹ * coreGeneratorA := by
          rw [generatorB_sq, mul_one, mul_inv_cancel, one_mul]
        _ = _ := by group
    conv_lhs => rw [he]
    rw [map_mul, map_mul, hag' wordL wordL_mem, hb,
      hag' _ generatorA_bridge_mem, ← map_mul, ← map_mul, ← he]
  apply MonoidHom.eq_of_eqOn_dense coreGenerators_closure_eq_top
  rintro g (rfl | rfl)
  · exact ha
  · exact hb

/-- The actual intertwining equivalence obtained from point-stabilizer agreement. -/
def equivOfPointStabilizerAgreement
    (τ : Representation (ZMod 2) M22TripleCover BinarySpace)
    (hag : ∀ g : pointStabilizer, τ g = binaryRepresentation g) :
    Representation.Equiv τ binaryRepresentation := by
  apply equivOfGenerators τ binaryRepresentation (LinearEquiv.refl (ZMod 2) BinarySpace)
  · intro v
    rw [eq_of_pointStabilizer_agreement τ hag]
    rfl
  · intro v
    rw [eq_of_pointStabilizer_agreement τ hag]
    rfl

/-- Extension rigidity in the form consumed by James uniqueness assembly. -/
theorem extension_equiv
    (τ : Representation (ZMod 2) M22TripleCover BinarySpace)
    (_hf : Function.Injective τ) (_hi : τ.IsIrreducible)
    (hag : ∀ g : pointStabilizer, τ g = binaryRepresentation g) :
    Nonempty (Representation.Equiv τ binaryRepresentation) :=
  ⟨equivOfPointStabilizerAgreement τ hag⟩

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointExtension
