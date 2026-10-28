module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.HighestWeight

/-!
# Uniqueness and intertwiners for left highest weights

Apply the checked rational highest-weight arguments at the raw label `-a`.
The actual vectors, Borel, actions and finite inclusion are unchanged.
Source: GLS3 1.14.6(c) and the equal-weight direction of 2.8.2.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

theorem leftHighestWeight_unique (S : Geometry K) (A : RationalFactor K)
    {a b : Weight} (ha : HasLeftHighestWeight S A a) (hb : HasLeftHighestWeight S A b) :
    a = b := neg_injective (highestWeight_unique S A ha hb)

theorem rational_equivalent_of_leftHighestWeight_eq (S : Geometry K)
    (A C : RationalFactor K) {a b : Weight}
    (ha : HasLeftHighestWeight S A a) (hb : HasLeftHighestWeight S C b) (hab : a = b) :
    AreEquivalentRepresentations A.action C.action :=
  rational_equivalent_of_highestWeight_eq S A C ha hb (congrArg Neg.neg hab)

theorem leftHighestWeight_of_equivalent (S : Geometry K) (A C : RationalFactor K)
    {a : Weight} (ha : HasLeftHighestWeight S A a)
    (he : AreEquivalentRepresentations A.action C.action) : HasLeftHighestWeight S C a :=
  highestWeight_of_equivalent S A C ha he

theorem rational_equivalent_iff_leftHighestWeight_eq (S : Geometry K)
    (A C : RationalFactor K) {a b : Weight}
    (ha : HasLeftHighestWeight S A a) (hb : HasLeftHighestWeight S C b) :
    AreEquivalentRepresentations A.action C.action ↔ a = b :=
  (rational_equivalent_iff_highestWeight_eq S A C ha hb).trans neg_inj

theorem restriction_equivalent_of_leftHighestWeight_eq (S : Geometry K)
    (A C : RationalFactor K) {a b : Weight}
    (ha : HasLeftHighestWeight S A a) (hb : HasLeftHighestWeight S C b) (hab : a = b)
    (n : ℕ) :
    Nonempty (Representation.Equiv (A.restrict (S.inclusion n)).ρ
      (C.restrict (S.inclusion n)).ρ) :=
  restriction_equivalent_of_highestWeight_eq S A C ha hb (congrArg Neg.neg hab) n

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
