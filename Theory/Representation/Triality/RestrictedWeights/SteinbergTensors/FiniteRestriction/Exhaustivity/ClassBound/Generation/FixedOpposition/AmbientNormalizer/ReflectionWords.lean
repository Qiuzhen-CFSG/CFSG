module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedSubgroups
public import Theory.AlgebraicGroup.Tori.Character.Duality

/-!
# Lifting the D4 opposition word to the supplied torus

The cube of the Coxeter word `[0, 1, 2, 3]` negates every integral D4 weight.
Given actual ambient representatives for its four simple reflections, we
multiply those representatives in the order dictated by inverse conjugation.
Character separation on the supplied torus then proves simultaneous inversion
by that one product. The four representatives remain explicit geometric inputs;
an abstract Weyl action or pointwise conjugacy does not supply them.

Source: GLS3, Chapter 1, Remark 1.8.9 and Theorem 1.9.5(f);
`refs/KGroup/GLS3/Chapter2St2.tex`, the torus-inversion step of 12.4.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight

/-- A twelve-reflection word for minus identity in the marked D4 system. -/
def oppositionWord : List (Fin 4) := [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]

/-- The word acts by negation on all integral weights, not only on roots. -/
theorem oppositionWord_neg (a : Weight) : wordAction a oppositionWord = -a := by
  funext j
  fin_cases j <;>
    simp [wordAction, oppositionWord, reflection, typeDCartanMatrix] <;> ring

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Actual simple-reflection lifts on the supplied torus. The point equation
uses inverse conjugation, as does `RootWeightEquation`. Construction of this
data from `Geometry` is a separate obligation, not a field of `Geometry`. -/
structure SimpleReflectionLifts (S : Geometry K) where
  representative : Fin 4 → Variety.Point K
  torusMap : Fin 4 → Variety.Point S.torus.carrierVariety →
    Variety.Point S.torus.carrierVariety
  conjugation : ∀ i t, S.torus.includePoint t * representative i =
    representative i * S.torus.includePoint (torusMap i t)
  character : ∀ i a t,
    (S.weight (Multiplicative.ofAdd a)).pointCharacter (torusMap i t) =
      (S.weight (Multiplicative.ofAdd (reflection i a))).pointCharacter t

/-- The ambient product whose inverse conjugation realizes a reflection word.
The reversed multiplication order matches `D4RestrictedWeight.wordAction`. -/
def SimpleReflectionLifts.representativeWord {S : Geometry K}
    (D : SimpleReflectionLifts S) : List (Fin 4) → Variety.Point K
  | [] => 1
  | i :: w => D.representativeWord w * D.representative i

/-- The corresponding composition on actual torus points. -/
def SimpleReflectionLifts.torusWord {S : Geometry K}
    (D : SimpleReflectionLifts S) : List (Fin 4) →
      Variety.Point S.torus.carrierVariety → Variety.Point S.torus.carrierVariety
  | [], t => t
  | i :: w, t => D.torusMap i (D.torusWord w t)

omit [IsAlgClosed k] in
/-- Multiplying the supplied ambient lifts realizes the composed torus map. -/
theorem SimpleReflectionLifts.word_conjugation {S : Geometry K}
    (D : SimpleReflectionLifts S) (w : List (Fin 4))
    (t : Variety.Point S.torus.carrierVariety) :
    S.torus.includePoint t * D.representativeWord w =
      D.representativeWord w * S.torus.includePoint (D.torusWord w t) := by
  induction w with
  | nil => simp [representativeWord, torusWord]
  | cons i w ih =>
    dsimp only [representativeWord, torusWord]
    calc
      _ = (S.torus.includePoint t * D.representativeWord w) * D.representative i :=
        (mul_assoc _ _ _).symm
      _ = (D.representativeWord w * S.torus.includePoint (D.torusWord w t)) *
          D.representative i := by rw [ih]
      _ = D.representativeWord w *
          (S.torus.includePoint (D.torusWord w t) * D.representative i) := mul_assoc _ _ _
      _ = D.representativeWord w *
          (D.representative i * S.torus.includePoint (D.torusMap i (D.torusWord w t))) := by
        rw [D.conjugation]
      _ = _ := (mul_assoc _ _ _).symm

omit [IsAlgClosed k] in
/-- The composed torus map acts by the same word on the actual characters. -/
theorem SimpleReflectionLifts.word_character {S : Geometry K}
    (D : SimpleReflectionLifts S) (w : List (Fin 4)) (a : Weight)
    (t : Variety.Point S.torus.carrierVariety) :
    (S.weight (Multiplicative.ofAdd a)).pointCharacter (D.torusWord w t) =
      (S.weight (Multiplicative.ofAdd (wordAction a w))).pointCharacter t := by
  induction w generalizing a with
  | nil => rfl
  | cons i w ih =>
    rw [torusWord, D.character, ih]
    rfl

private theorem torusPoint_ext_weight (S : Geometry K)
    {t v : Variety.Point S.torus.carrierVariety}
    (h : ∀ a : Weight, (S.weight (Multiplicative.ofAdd a)).pointCharacter t =
      (S.weight (Multiplicative.ofAdd a)).pointCharacter v) : t = v := by
  apply (torusPointEval_bijective S.maximalTorus.1).1
  ext χ
  obtain ⟨a, rfl⟩ := S.weight.surjective χ
  exact h a.toAdd

/-- Character separation upgrades the weight calculation to inversion of
every actual torus point. -/
theorem SimpleReflectionLifts.opposition_torusWord {S : Geometry K}
    (D : SimpleReflectionLifts S) (t : Variety.Point S.torus.carrierVariety) :
    D.torusWord oppositionWord t = t⁻¹ := by
  apply torusPoint_ext_weight S
  intro a
  rw [D.word_character, oppositionWord_neg]
  have hneg : S.weight (Multiplicative.ofAdd (-a)) =
      (S.weight (Multiplicative.ofAdd a))⁻¹ := S.weight.map_inv _
  rw [hneg]
  change ((torusPointEval _ t) ((S.weight (Multiplicative.ofAdd a))⁻¹) : k) =
    ((torusPointEval _ t⁻¹) (S.weight (Multiplicative.ofAdd a)) : k)
  simp only [map_inv, MonoidHom.inv_apply]

/-- One specified ambient element, independent of the torus point. -/
def SimpleReflectionLifts.oppositionRepresentative {S : Geometry K}
    (D : SimpleReflectionLifts S) : Variety.Point K :=
  (D.representativeWord oppositionWord)⁻¹

/-- The actual product of simple-reflection lifts simultaneously inverts the
entire supplied torus. No fixed-point or elementary-generation premise is used. -/
theorem SimpleReflectionLifts.oppositionRepresentative_inverts {S : Geometry K}
    (D : SimpleReflectionLifts S) (t : Variety.Point K) (ht : t ∈ S.torus) :
    D.oppositionRepresentative * t * D.oppositionRepresentative⁻¹ = t⁻¹ := by
  obtain ⟨x, rfl⟩ := (Set.ext_iff.mp S.torus.range_inclusion t).mpr ht
  change (D.representativeWord oppositionWord)⁻¹ * S.torus.includePoint x *
    ((D.representativeWord oppositionWord)⁻¹)⁻¹ = _
  rw [inv_inv]
  have h := D.word_conjugation oppositionWord x
  rw [D.opposition_torusWord] at h
  calc
    _ = (D.representativeWord oppositionWord)⁻¹ *
      (S.torus.includePoint x * D.representativeWord oppositionWord) := mul_assoc _ _ _
    _ = (D.representativeWord oppositionWord)⁻¹ *
      (D.representativeWord oppositionWord * S.torus.includePoint x⁻¹) := by rw [h]
    _ = S.torus.includePoint x⁻¹ := by group
    _ = _ := map_inv S.torus.inclusion.onPoints x

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer
