module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Geometry
public import Theory.AlgebraicGroup.Borel.HighestWeight

/-!
# Highest-weight uniqueness before finite restriction

An actual opposite-Borel big cell identifies rational irreducibles with the
same highest weight by a linear intertwining equivalence. Such an equivalence
restricts along the literal elementary inclusion for every exponent, including
one. Conversely, equivalence of the rational actions identifies their highest
weights. Equivalence of the finite restrictions alone is a separate obligation.

Sources: GLS3, Theorem 1.14.6(c) and the equal-weight direction of Theorem 2.8.2.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Two highest vectors of a rational irreducible have the same actual weight. -/
theorem highestWeight_unique (S : Geometry K) (A : RationalFactor K)
    {a b : Weight} (ha : HasHighestWeight S A a) (hb : HasHighestWeight S A b) :
    a = b := by
  obtain ⟨v, hv⟩ := ha
  obtain ⟨w, hw⟩ := hb
  obtain ⟨c, _, hwv⟩ := irreducible_highWeight_unique_line_of_oppositeBorelBigCell
    S.bigCell S.maximalTorus A.action A.irreducible v w
    (S.coordinateEmbedding a) (S.coordinateEmbedding b) hv hw
  apply S.coordinateEmbedding.injective
  apply TorusCharacter.pointCharacter_injective
  ext t
  have heq : (A.action.action (S.torus.includePoint t)).1 w =
      (S.coordinateEmbedding a).pointCharacter t • w := by
    rw [hwv, map_smul, hv.2.2 t]
    exact smul_comm _ _ _
  exact smul_left_injective k hw.1.1 (heq.symm.trans (hw.2.2 t))

/-- Equal highest weights give an actual algebraic intertwining equivalence. -/
theorem rational_equivalent_of_highestWeight_eq (S : Geometry K)
    (A C : RationalFactor K) {a b : Weight}
    (ha : HasHighestWeight S A a) (hb : HasHighestWeight S C b) (hab : a = b) :
    AreEquivalentRepresentations A.action C.action := by
  subst b
  obtain ⟨v, hv⟩ := ha
  obtain ⟨w, hw⟩ := hb
  exact irreducible_highWeight_equivalent_of_oppositeBorelBigCell
    S.bigCell S.maximalTorus A.action C.action A.irreducible C.irreducible
    v w (S.coordinateEmbedding a) hv hw

/-- An algebraic intertwining equivalence carries a highest vector to a
highest vector for the same Borel and torus character. -/
theorem highestWeight_of_equivalent (S : Geometry K) (A C : RationalFactor K)
    {a : Weight} (ha : HasHighestWeight S A a)
    (he : AreEquivalentRepresentations A.action C.action) : HasHighestWeight S C a := by
  obtain ⟨v, hv⟩ := ha
  obtain ⟨e, he⟩ := he
  have hne : e v ≠ 0 := by simpa using hv.1.1
  refine ⟨e v, ⟨hne, ?_⟩, hne, ?_⟩
  · intro g hg
    obtain ⟨c, hc⟩ := hv.1.2 g hg
    refine ⟨c, ?_⟩
    calc
      (C.action.action g).1 (e v) = e ((A.action.action g).1 v) := (he g v).symm
      _ = c • e v := by rw [hc, e.map_smul]
  · intro t
    calc
      (C.action.action (S.torus.includePoint t)).1 (e v) =
          e ((A.action.action (S.torus.includePoint t)).1 v) :=
        (he (S.torus.includePoint t) v).symm
      _ = (S.coordinateEmbedding a).pointCharacter t • e v := by
        rw [hv.2.2 t, e.map_smul]

/-- This equivalence concerns the full rational actions. The analogous
finite-restriction converse must still be proved. -/
theorem rational_equivalent_iff_highestWeight_eq (S : Geometry K)
    (A C : RationalFactor K) {a b : Weight}
    (ha : HasHighestWeight S A a) (hb : HasHighestWeight S C b) :
    AreEquivalentRepresentations A.action C.action ↔ a = b := by
  exact ⟨fun he => highestWeight_unique S C (highestWeight_of_equivalent S A C ha he) hb,
    rational_equivalent_of_highestWeight_eq S A C ha hb⟩

/-- The equal-weight direction for the actual elementary restrictions.
It needs no equality between elementary and fixed-point groups. -/
theorem restriction_equivalent_of_highestWeight_eq (S : Geometry K)
    (A C : RationalFactor K) {a b : Weight}
    (ha : HasHighestWeight S A a) (hb : HasHighestWeight S C b) (hab : a = b)
    (n : ℕ) :
    Nonempty (Representation.Equiv (A.restrict (S.inclusion n)).ρ
      (C.restrict (S.inclusion n)).ρ) := by
  obtain ⟨e, he⟩ := rational_equivalent_of_highestWeight_eq S A C ha hb hab
  exact ⟨restrictEquiv A C e he (S.inclusion n)⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
