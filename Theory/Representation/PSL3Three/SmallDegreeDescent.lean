module

public import Theory.Representation.EndFieldDegree
public import Theory.SpecificGroups.PSL3Three.Basic

/-!
# Scalar descent for the small characteristic-two PSL₃(3) degrees

The small absolute-degree calculation and the field-of-definition calculation
are independent inputs. Over the actual Schur endomorphism field, the former
leaves degree twelve or sixteen. In the second case the latter forces at least
two binary scalar dimensions, hence binary degree at least thirty-two. In the
first case a binary degree at most eighteen forces the scalar degree to be one.

This proves the descent step, not the character-table inputs. In particular,
binary irreducibility is not replaced by an assumed absolute irreducibility.
The source application is GM02, Classification of 2F-modules I, Proposition
4.2, manuscript pp.9–10; its table and field restrictions remain to be proved.
-/

public section
open scoped MonoidAlgebra

namespace Representation.PSL3Three
universe v

/-- The small faithful absolute degrees on the actual projective matrix group.
This is an input contract, not an asserted character-table theorem. -/
@[expose] def AbsoluteDegreeWindow : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (W : Type v) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (σ : Representation K Matrix.PSL3Three.PSL W), Function.Injective σ →
    IsAbsolutelyIrreducible σ → Module.finrank K W ≤ 18 →
      Module.finrank K W = 12 ∨ Module.finrank K W = 16

/-- Degree sixteen is not defined over the binary prime field. The actual
character field is larger still; this weaker restriction suffices for descent. -/
@[expose] def DegreeSixteenFieldObstruction : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (W : Type v) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (σ : Representation K Matrix.PSL3Three.PSL W), Function.Injective σ →
    IsAbsolutelyIrreducible σ → Module.finrank K W = 16 → 2 < Nat.card K

/-- Descent of the two explicit native calculations to an arbitrary irreducible
binary module. No absolute irreducibility of the input representation is assumed. -/
theorem binary_degree_twelve_of_absolute_calculations
    (hdegrees : AbsoluteDegreeWindow.{v})
    (hfield : DegreeSixteenFieldObstruction.{v})
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) Matrix.PSL3Three.PSL V) [IsIrreducible ρ]
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 18) :
    Module.finrank (ZMod 2) V = 12 := by
  let E := Module.End (ZMod 2)[Matrix.PSL3Three.PSL] ρ.asModule
  let : Finite ρ.asModule := Module.finite_of_finite (ZMod 2)
  let : FiniteDimensional E ρ.asModule := Module.Finite.of_finite
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  let : CharP E 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  have hfE := (endFieldRep_injective_iff ρ).mpr hf
  have ha := endFieldRep_isAbsolutelyIrreducible ρ
  have hdim := hdegrees E ρ.asModule ρ.endFieldRep hfE ha
    ((endField_finrank_le ρ).trans hd)
  have ht := finrank_eq_endField_mul ρ
  change Module.finrank (ZMod 2) V =
    Module.finrank (ZMod 2) E * Module.finrank E ρ.asModule at ht
  have hepos : 0 < Module.finrank (ZMod 2) E := Module.finrank_pos
  rcases hdim with htwelve | hsixteen
  · rw [htwelve] at ht
    omega
  · have hcard := hfield E ρ.asModule ρ.endFieldRep hfE ha hsixteen
    have he : 2 ≤ Module.finrank (ZMod 2) E := by
      by_contra hh
      have heone : Module.finrank (ZMod 2) E = 1 := by omega
      have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)
      rw [Nat.card_zmod, heone, pow_one] at hc
      omega
    rw [hsixteen] at ht
    omega

end Representation.PSL3Three
