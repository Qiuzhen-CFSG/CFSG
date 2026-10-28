module

public import Theory.Representation.Mathieu.SmallModules.Models
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PrimeRestriction
public import Theory.Mathieu.M12.Properties.Order

/-!
# Point restriction and assembly for binary M₁₂ recognition

The actual M₁₁ embeds as the stabilizer of point twelve in M₁₂. A faithful
binary representation of degree at most ten restricts irreducibly to it,
by the order-eleven argument. Its comparison module is the restriction of
the actual augmentation quotient `M12Heart`, with the same group marking.

Given an equivalence on M₁₁, coordinate transport makes this restriction
agree literally with the reference action. Rigidity of the full actions
extending it then supplies the requested M₁₂ equivalence, retaining any
change of group marking produced by that rigidity theorem.

The M₁₁ classification and extension rigidity are explicit outstanding
premises. This module does not claim the James completeness theorem.

Source: Aschbacher--Smith, G.7.3(2), printed p.348 (PDF p.359), citing
G. D. James, J. Algebra 27 (1973), 57--111.
-/

@[expose] public section

namespace Representation.MathieuSmall.M12Recognition
open Sporadic.Mathieu

/-- The literal M₁₁ point stabilizer inclusion in the twelve-point M₁₂ action. -/
noncomputable def pointEmbedding : M11 →* M12 :=
  (MulAction.stabilizer M12 (12 : Fin 12)).subtype.comp
    m11ToM12PointStabilizer

theorem pointEmbedding_injective : Function.Injective pointEmbedding :=
  Subtype.val_injective.comp m11ToM12PointStabilizer_injective

/-- Restriction of the actual ten-dimensional heart to that marked M₁₁. -/
noncomputable def pointRepresentation : Representation (ZMod 2) M11 M12Heart :=
  m12HeartRepresentation.comp pointEmbedding

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) M12 V)

/-- The faithful small-degree branch has dimension exactly ten. -/
theorem finrank_eq_ten [FiniteDimensional (ZMod 2) V] (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 10) : Module.finrank (ZMod 2) V = 10 := by
  have hlo := BinaryPrimeDegree.orderOf_le_finrank ρ hf (by decide : Nat.Prime 11)
    (by decide : 11 ≠ 2) (by rw [m12_order]; norm_num : 11 ∣ Nat.card M12)
  rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo
  omega

/-- Restriction to the actual M₁₁ is irreducible; no semisimplicity or
irreducibility of the original action is assumed. -/
theorem point_restriction_isIrreducible [FiniteDimensional (ZMod 2) V] (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 10) :
    Representation.IsIrreducible (ρ.comp pointEmbedding) :=
  irreducible_of_eleven_dvd (ρ.comp pointEmbedding)
    (hf.comp pointEmbedding_injective) hd (by rw [m11_order]; norm_num)

/-- Write the full M₁₂ action in the coordinates of a restricted-module equivalence. -/
noncomputable def coordinateRepresentation (e : V ≃ₗ[ZMod 2] M12Heart) :
    Representation (ZMod 2) M12 M12Heart where
  toFun g := e.conj (ρ g)
  map_one' := by ext v; simp [LinearEquiv.conj_apply]
  map_mul' g h := by ext v; simp [LinearEquiv.conj_apply, map_mul]

/-- Coordinate transport intertwines the entire original action. -/
noncomputable def coordinateEquiv (e : V ≃ₗ[ZMod 2] M12Heart) :
    ρ.Equiv (coordinateRepresentation ρ e) :=
  .mk e (by intro g; ext v; simp [coordinateRepresentation, LinearEquiv.conj_apply])

theorem coordinateRepresentation_faithful (hf : Function.Injective ρ)
    (e : V ≃ₗ[ZMod 2] M12Heart) :
    Function.Injective (coordinateRepresentation ρ e) := by
  intro g h he
  exact hf (e.conj.injective he)

/-- An equivalence on the literal point stabilizer makes its matrices agree. -/
theorem coordinateRepresentation_on_point
    (e : Representation.Equiv (ρ.comp pointEmbedding) pointRepresentation) (g : M11) :
    coordinateRepresentation ρ e.toLinearEquiv (pointEmbedding g) =
      m12HeartRepresentation (pointEmbedding g) := by
  apply LinearMap.ext
  intro v
  change e (ρ (pointEmbedding g) (e.symm v)) =
    m12HeartRepresentation (pointEmbedding g) v
  have h := LinearMap.congr_fun (e.isIntertwining' g) (e.symm v)
  change e (ρ (pointEmbedding g) (e.symm v)) =
    m12HeartRepresentation (pointEmbedding g) (e (e.symm v)) at h
  simpa only [Representation.Equiv.apply_symm_apply] using h

/-- Conditional recognition from a point-restriction equivalence and rigidity
of extensions of that fixed point action. The resulting group marking is
retained. Both substantive inputs must be supplied before this proves
unconditional recognition. -/
theorem isM12Heart_of_point_inputs
    (hf : Function.Injective ρ)
    (hpoint : Nonempty (Representation.Equiv (ρ.comp pointEmbedding) pointRepresentation))
    (hextension : ∀ τ : Representation (ZMod 2) M12 M12Heart,
      Function.Injective τ → τ.IsIrreducible →
      (∀ g : M11, τ (pointEmbedding g) = m12HeartRepresentation (pointEmbedding g)) →
      IsM12Heart τ) : IsM12Heart ρ := by
  obtain ⟨e⟩ := hpoint
  have hfaith := coordinateRepresentation_faithful ρ hf e.toLinearEquiv
  have hirr := irreducible_of_eleven_dvd (coordinateRepresentation ρ e.toLinearEquiv)
    hfaith finrank_m12Heart.le (by rw [m12_order]; norm_num)
  obtain ⟨a, ⟨f⟩⟩ := hextension (coordinateRepresentation ρ e.toLinearEquiv) hfaith hirr
    (coordinateRepresentation_on_point ρ e)
  exact ⟨a, ⟨(coordinateEquiv ρ e.toLinearEquiv).trans f⟩⟩

end Representation.MathieuSmall.M12Recognition
