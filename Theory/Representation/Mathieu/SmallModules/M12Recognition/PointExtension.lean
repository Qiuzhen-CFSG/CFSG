module
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointExtension.Centralizer

/-!
# Rigidity of the binary M₁₂ heart extension

Literal agreement with the heart representation on the marked M₁₁ point
stabilizer determines the entire M₁₂ representation. For the extra generator
t, the defect R(t)⁻¹τ(t) centralizes the three certified intersection words.
Its only invertible possibilities are the identity and a coordinate swap.
The swap violates the relation (ta)⁵ = 1. Agreement on t and maximality of
the point stabilizer then give equality on M₁₂.

The last theorem applies this rigidity to the actual coordinate transport
in `Reduction`. The independent M₁₁ module classification remains with the
recognition assembly owner. The identity group marking is retained throughout;
no action of Aut(M₁₂) on twelve points is assumed.

Source context: Aschbacher--Smith G.7.3(2), printed p.348 (PDF p.359), citing
G. D. James, J. Algebra 27 (1973), 57--111.
-/

public section
namespace Representation.MathieuSmall.M12Recognition.PointExtension
open Sporadic.Mathieu BinaryPermutation

private theorem defect_commutes
    (τ : Representation (ZMod 2) M12 M12Heart)
    (hpoint : ∀ g : M11, τ (pointEmbedding g) = m12HeartRepresentation (pointEmbedding g))
    (k : Fin 3) :
    Commute (m12HeartRepresentation t⁻¹ * τ t)
      (m12HeartRepresentation (intersectionWord k)) := by
  let R := m12HeartRepresentation
  let w := intersectionWord k
  have hw : τ w = R w := agree_on_stabilizer τ hpoint w (intersectionWord_mem k)
  have hc : τ (t * w * t⁻¹) = R (t * w * t⁻¹) :=
    agree_on_stabilizer τ hpoint _ (conjugateWord_mem k)
  simp only [map_mul, hw] at hc
  have hτ : τ t⁻¹ * τ t = 1 := by rw [← map_mul]; simp
  have hR : R t⁻¹ * R t = 1 := by rw [← map_mul]; simp
  change (R t⁻¹ * τ t) * R w = R w * (R t⁻¹ * τ t)
  calc
    (R t⁻¹ * τ t) * R w = R t⁻¹ * ((τ t * R w * τ t⁻¹) * τ t) := by
      simp only [mul_assoc, hτ, mul_one]
    _ = R t⁻¹ * ((R t * R w * R t⁻¹) * τ t) := by rw [hc]
    _ = R w * (R t⁻¹ * τ t) := by
      simp only [← mul_assoc, hR, one_mul]


private theorem wrong_fifth :
    ((naturalRepresentation (Fin 12))
      (m12GeneratorA * Equiv.swap 0 6 * aPerm)) ^ 5 ≠ 1 := by
  intro he
  rw [← map_pow] at he
  have hm := congrArg (fun f => matrixEquivalence f 5 5) he
  rw [matrix_natural, map_one] at hm
  have hz : rawCoordinates
      (representation (Fin 12) ((m12GeneratorA * Equiv.swap 0 6 * aPerm) ^ 5)
        (representative (Pi.single (5 : Fin 10) 1))) 5 = 0 := by
    decide +kernel
  rw [hz] at hm
  exact zero_ne_one hm

/-- Literal agreement on the marked point stabilizer determines the whole M₁₂
representation. Faithfulness and irreducibility are not needed for this step. -/
theorem eq_of_point_agreement
    (τ : Representation (ZMod 2) M12 M12Heart)
    (hpoint : ∀ g : M11, τ (pointEmbedding g) = m12HeartRepresentation (pointEmbedding g)) :
    τ = m12HeartRepresentation := by
  apply eq_of_agree_on_t τ hpoint
  let D := m12HeartRepresentation t⁻¹ * τ t
  have hu : IsUnit D := ((Group.isUnit t⁻¹).map m12HeartRepresentation).mul ((Group.isUnit t).map τ)
  have hc : ∀ k, Commute (matrixEquivalence D) (wordMatrix k) := by
    intro k
    have he := (defect_commutes τ hpoint k).map matrixEquivalence
    have hm : matrixEquivalence (m12HeartRepresentation (intersectionWord k)) = wordMatrix k := by
      change matrixEquivalence (naturalRepresentation (Fin 12)
        (intersectionWord k : Equiv.Perm (Fin 12))) = _
      rw [matrix_natural_eq, intersectionWord_perm, wordMatrix_check]
    simpa only [hm] using he
  have cancel_defect : m12HeartRepresentation t * D = τ t := by
    change m12HeartRepresentation t * (m12HeartRepresentation t⁻¹ * τ t) = τ t
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rcases centralizer_units (matrixEquivalence D) (hu.map matrixEquivalence) hc with he | he
  · have hd : D = 1 := matrixEquivalence.injective (by simpa only [map_one] using he)
    rw [hd, mul_one] at cancel_defect
    exact cancel_defect.symm
  · have hd : D = naturalRepresentation (Fin 12) (Equiv.swap 0 6) := by
      apply matrixEquivalence.injective
      rw [matrix_natural_eq, swapMatrix_check]
      exact he
    rw [hd] at cancel_defect
    have hp : (τ t * τ a) ^ 5 = 1 := by
      rw [← map_mul, ← map_pow, ta_fifth, map_one]
    rw [← cancel_defect, show τ a = m12HeartRepresentation a from
      hpoint m11GeneratorAInM11] at hp
    have hm : m12HeartRepresentation t * naturalRepresentation (Fin 12) (Equiv.swap 0 6) *
        m12HeartRepresentation a =
        naturalRepresentation (Fin 12) (m12GeneratorA * Equiv.swap 0 6 * aPerm) := by
      change naturalRepresentation (Fin 12) m12GeneratorA *
        naturalRepresentation (Fin 12) (Equiv.swap 0 6) *
        naturalRepresentation (Fin 12) (a : Equiv.Perm (Fin 12)) = _
      rw [← map_mul, ← map_mul, a_perm]
    rw [hm] at hp
    exact False.elim (wrong_fifth hp)

/-- The extension-rigidity contract, retaining the actual identity group marking. -/
theorem isM12Heart_of_agree_on_point
    (τ : Representation (ZMod 2) M12 M12Heart)
    (hpoint : ∀ g : M11, τ (pointEmbedding g) = m12HeartRepresentation (pointEmbedding g)) :
    IsM12Heart τ := by
  rw [eq_of_point_agreement τ hpoint]
  exact ⟨MulEquiv.refl M12, ⟨Representation.Equiv.refl _⟩⟩

/-- Apply the proved extension theorem to the literal coordinate transport in
`Reduction`. Only the independent M₁₁ classification input remains. -/
theorem isM12Heart_of_point_equivalence
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) M12 V) (hf : Function.Injective ρ)
    (hpoint : Nonempty (Representation.Equiv (ρ.comp pointEmbedding) pointRepresentation)) :
    IsM12Heart ρ :=
  isM12Heart_of_point_inputs ρ hf hpoint
    (fun τ _ _ h => isM12Heart_of_agree_on_point τ h)

end Representation.MathieuSmall.M12Recognition.PointExtension
