module
public import Theory.Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra
public import Theory.Representation.JankoTwo.SixDimensionalCertificate.LocalTraceCover
public import Theory.Representation.IrreducibleTraceEquivalence

/-!
# Completeness of the two Hall--Janko degree-six trace characters

The checked outer marking carries a nonzero weight line of either surviving
pattern to a weight absent from that same pattern, so it swaps the two patterns.
Equal patterns give equal traces on the torus, both cubic classes, the septic
class and the mixed order-fifteen elements. The proved odd-class coverage and
p-regular trace reduction therefore give equality on the whole literal carrier.
The inner factor in the marking disappears on characters, retaining exactly
`ExceptionalParabolics.involutionAut` in the conclusion. Simple-module density
then gives actual equivalences; local geometry proves the needed irreducibility.

Every spectral and coverage premise is discharged. No representation catalogue,
carrier identification or simplicity hypothesis is assumed. The finite group
identities and exhaustive class cover use the degree-100 ATLAS generators.

Source application: Aschbacher--Smith K.4.5, printed p.460/PDF p.471;
Hiss--Malle corrected Table 2, characteristic-two degree-six J₂ entry.
See Source.md for the local proof route and the imported certificates for
permutation attribution. Scalar and concrete-model descent are in ScalarDescent.
-/

public section
namespace Representation.JankoTwo.SixDimensionalCertificate
open Sporadic.LeechRelated.J2 LocalSpectra
variable {E U : Type*} [Field E] [AddCommGroup U] [Module E U]

/-- The literal outer marking sends each simultaneous weight into its computed image. -/
theorem weightSpace_le_outerTwist (ρ : Representation E Carrier U)
    {ζ : E} (hζ : IsPrimitiveRoot ζ 5) (w : Weights.Weight) :
    weightSpace ρ ζ w ≤
      weightSpace (ρ.comp TraceGeometry.outerTwist.toMonoidHom) ζ (Weights.outerMap w) := by
  intro v hv
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    change ρ (TraceGeometry.outerTwist TraceGeometry.x) v = _
    rw [TraceGeometry.outerTwist_x, torus_action ρ ζ w 3 2 hv]
    have he : (Weights.outerMap w).1.val = (w.1.val * 3 + w.2.val * 2) % 5 := by
      norm_num [Weights.outerMap, ZMod.val_add, ZMod.val_mul, ZMod.val_ofNat,
        Nat.add_mod, Nat.mul_mod, Nat.mul_comm]
    rw [he, ← pow_eq_pow_mod _ hζ.pow_eq_one]
  · apply Module.End.mem_eigenspace_iff.mpr
    change ρ (TraceGeometry.outerTwist TraceGeometry.y) v = _
    rw [TraceGeometry.outerTwist_y]
    have h := torus_action ρ ζ w 0 2 hv
    simp only [pow_zero, one_mul, Nat.mul_zero, zero_add] at h
    rw [h]
    have he : (Weights.outerMap w).2.val = (w.2.val * 2) % 5 := by
      norm_num [Weights.outerMap, ZMod.val_mul, ZMod.val_ofNat, Nat.mul_comm]
    rw [he, ← pow_eq_pow_mod _ hζ.pow_eq_one]

/-- The checked outer marking interchanges the two surviving weight patterns. -/
theorem outerTwist_pattern [CharP E 2] [IsAlgClosed E] [FiniteDimensional E U]
    (ρ : Representation E Carrier U) (hρ : Function.Injective ρ)
    (hdim : Module.finrank E U = 6) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (i : Fin 4) (hi : i = 0 ∨ i = 1)
    (hpat : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w) :
    ∀ w, weightMultiplicity (ρ.comp TraceGeometry.outerTwist.toMonoidHom) ζ w =
      Weights.pattern (Weights.swap i) w := by
  have hle (w : Weights.Weight) := Submodule.finrank_mono (weightSpace_le_outerTwist ρ hζ w)
  simp only [finrank_weightSpace, hpat] at hle
  have hf : Function.Injective (ρ.comp TraceGeometry.outerTwist.toMonoidHom) :=
    by
      intro a b h
      exact TraceGeometry.outerTwist.injective (hρ h)
  rcases two_patterns (ρ.comp TraceGeometry.outerTwist.toMonoidHom) hf hdim hζ with h0 | h1
  · rcases hi with rfl | rfl
    · have hh := hle (Weights.seed 0)
      rw [h0] at hh
      have hleft : Weights.pattern 0 (Weights.seed 0) = 1 := by decide +kernel
      have hright : Weights.pattern 0 (Weights.outerMap (Weights.seed 0)) = 0 := by decide +kernel
      omega
    · simpa only [show Weights.swap 1 = 0 from rfl] using h0
  · rcases hi with rfl | rfl
    · simpa only [show Weights.swap 0 = 1 from rfl] using h1
    · have hh := hle (Weights.seed 1)
      rw [h1] at hh
      have hleft : Weights.pattern 1 (Weights.seed 1) = 1 := by decide +kernel
      have hright : Weights.pattern 1 (Weights.outerMap (Weights.seed 1)) = 0 := by decide +kernel
      omega
end Representation.JankoTwo.SixDimensionalCertificate

namespace Representation.JankoTwo.SixDimensionalCertificate
open Sporadic.LeechRelated.J2 LocalSpectra

section Comparison
universe v
variable {W U : Type v} {E : Type*} [Field E] [CharP E 2] [IsAlgClosed E]
  [AddCommGroup U] [Module E U] [FiniteDimensional E U]
  [AddCommGroup W] [Module E W] [FiniteDimensional E W]

/-- Equal surviving weight patterns determine every trace on the literal carrier. -/
theorem character_eq_of_pattern
    (ρ : Representation E Carrier U) (σ : Representation E Carrier W)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (hdρ : Module.finrank E U = 6) (hdσ : Module.finrank E W = 6)
    {ζ : E} (hζ : IsPrimitiveRoot ζ 5) (i : Fin 4) (hi : i = 0 ∨ i = 1)
    (hpρ : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w)
    (hpσ : ∀ w, weightMultiplicity σ ζ w = Weights.pattern i w) :
    ρ.character = σ.character := by
  apply LocalTraceCover.character_eq_of_local
  · intro a b
    exact (character_torus_of_pattern ρ hζ i hpρ a.val b.val).trans
      (character_torus_of_pattern σ hζ i hpσ a.val b.val).symm
  · exact (character_c ρ hρ hdρ hζ).trans (character_c σ hσ hdσ hζ).symm
  · exact (character_r_sq ρ hρ hdρ hζ).trans (character_r_sq σ hσ hdσ hζ).symm
  · exact (character_ab ρ hρ hdρ TraceGeometry.orderOf_ab
      TraceGeometry.ab_isConj_square TraceGeometry.ab_isConj_inv).trans
      (character_ab σ hσ hdσ TraceGeometry.orderOf_ab
        TraceGeometry.ab_isConj_square TraceGeometry.ab_isConj_inv).symm
  · intro j
    rcases hi with rfl | rfl
    · exact (CubicExclusion.character_c_mul_x_pow_of_pattern_zero ρ hζ hpρ j.val).trans
        (CubicExclusion.character_c_mul_x_pow_of_pattern_zero σ hζ hpσ j.val).symm
    · exact (CubicExclusion.character_c_mul_x_pow_of_pattern_one ρ hζ hpρ j.val).trans
        (CubicExclusion.character_c_mul_x_pow_of_pattern_one σ hζ hpσ j.val).symm

/-- Completeness of the two trace possibilities, with the specified outer automorphism.
All spectral and conjugacy-coverage inputs are discharged. -/
theorem character_eq_or_involutionTwist
    (ρ : Representation E Carrier U) (σ : Representation E Carrier W)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (hdρ : Module.finrank E U = 6) (hdσ : Module.finrank E W = 6) :
    ρ.character = σ.character ∨
      ρ.character = Representation.character (σ.comp ExceptionalParabolics.involutionAut.toMonoidHom) := by
  let : NeZero (5 : E) := ⟨(CharP.cast_eq_zero_iff E 2 5).not.mpr (by decide)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot E 5
  obtain ⟨i, hi, hpρ⟩ : ∃ i : Fin 4, (i = 0 ∨ i = 1) ∧
      ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w := by
    rcases two_patterns ρ hρ hdρ hζ with h | h
    · exact ⟨0, Or.inl rfl, h⟩
    · exact ⟨1, Or.inr rfl, h⟩
  obtain ⟨j, hj, hpσ⟩ : ∃ j : Fin 4, (j = 0 ∨ j = 1) ∧
      ∀ w, weightMultiplicity σ ζ w = Weights.pattern j w := by
    rcases two_patterns σ hσ hdσ hζ with h | h
    · exact ⟨0, Or.inl rfl, h⟩
    · exact ⟨1, Or.inr rfl, h⟩
  by_cases he : i = j
  · subst j
    exact Or.inl (character_eq_of_pattern ρ σ hρ hσ hdρ hdσ hζ i hi hpρ hpσ)
  · have hs : Weights.swap j = i := by
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> first | rfl | exact (he rfl).elim
    have ht := outerTwist_pattern σ hσ hdσ hζ j hj hpσ
    rw [hs] at ht
    have hf : Function.Injective (σ.comp TraceGeometry.outerTwist.toMonoidHom) := by
      intro a b h
      exact TraceGeometry.outerTwist.injective (hσ h)
    exact Or.inr ((character_eq_of_pattern ρ
      (σ.comp TraceGeometry.outerTwist.toMonoidHom) hρ hf hdρ hdσ hζ i hi hpρ ht).trans
      (outerTwist_character σ))

/-- Every faithful degree-six action is equivalent to either a chosen one or its
specified outer twist; irreducibility is proved from the checked local geometry. -/
theorem equiv_or_involutionTwist
    (ρ : Representation E Carrier U) (σ : Representation E Carrier W)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (hdρ : Module.finrank E U = 6) (hdσ : Module.finrank E W = 6) :
    Nonempty (ρ.Equiv σ) ∨
      Nonempty (ρ.Equiv (σ.comp ExceptionalParabolics.involutionAut.toMonoidHom)) := by
  let : IsIrreducible ρ := isIrreducible_of_faithful_six ρ hρ hdρ
  let : IsIrreducible σ := isIrreducible_of_faithful_six σ hσ hdσ
  have hf : Function.Injective (σ.comp ExceptionalParabolics.involutionAut.toMonoidHom) := by
    intro a b h
    exact ExceptionalParabolics.involutionAut.injective (hσ h)
  let : IsIrreducible (σ.comp ExceptionalParabolics.involutionAut.toMonoidHom) :=
    isIrreducible_of_faithful_six _ hf hdσ
  exact (character_eq_or_involutionTwist ρ σ hρ hσ hdρ hdσ).imp
    (character_eq_iff_equiv_of_irreducible ρ σ).mp
    (character_eq_iff_equiv_of_irreducible ρ
      (σ.comp ExceptionalParabolics.involutionAut.toMonoidHom)).mp
end Comparison

end Representation.JankoTwo.SixDimensionalCertificate
