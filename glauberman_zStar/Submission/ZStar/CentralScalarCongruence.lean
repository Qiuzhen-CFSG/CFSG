import Submission.ZStar.BlockPreliminaries
import Submission.ZStar.CentralIdempotentSupport
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Congruence of localized central scalars

The ordinary block relation says that the central-character values of two
irreducible characters agree modulo the chosen cyclotomic prime.  Since a
central element is a linear combination of conjugacy-class sums, the same is
true for the scalar obtained by evaluating any localized central element.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar

namespace CentralScalarCongruence

open BlockPreliminaries

universe u

attribute [local instance] Fintype.ofFinite

variable {G : Type u} [Group G] [Finite G]

/-- A fixed representative of a conjugacy class. -/
noncomputable def classRepresentative (c : ConjClasses G) : G :=
  Classical.choose (ConjClasses.exists_rep c)

omit [Finite G] in
@[simp] theorem mk_classRepresentative (c : ConjClasses G) :
    ConjClasses.mk (classRepresentative c) = c :=
  Classical.choose_spec (ConjClasses.exists_rep c)

/-- The coefficient of a central group-algebra element on a conjugacy class.
Centrality guarantees that this does not depend on the chosen representative;
the fixed representative keeps the definition lightweight. -/
noncomputable def centralClassCoefficient
    {S : Type*} [CommRing S]
  (z : Subring.center (MonoidAlgebra S G))
  (c : ConjClasses G) : S :=
  (z : MonoidAlgebra S G) (classRepresentative c)

omit [Finite G] in
/-- The class coefficient agrees with the coefficient at every representative
of the class. -/
theorem centralClassCoefficient_eq
    {S : Type*} [CommRing S]
    (z : Subring.center (MonoidAlgebra S G))
    (c : ConjClasses G) (g : G) (hg : ConjClasses.mk g = c) :
    centralClassCoefficient z c = (z : MonoidAlgebra S G) g := by
  have hconj : IsConj g (classRepresentative c) := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj, hg, mk_classRepresentative]
  rcases isConj_iff.mp hconj with ⟨h, hh⟩
  exact (congrArg (z : G → S) hh).symm.trans
    (CentralIdempotentSupport.coeff_conj_eq_of_mem_center
      (z : MonoidAlgebra S G) z.property h g)

/-- Evaluation of a localized central group-algebra element under the
ordinary central character attached to `chi`. -/
noncomputable def localizedCentralScalar
    {eta : ℂ} (heta : IsPrimitiveRoot eta (Nat.card G))
    (P : Ideal (Representation.cyclotomicOrder eta)) [P.IsPrime]
    (chi : Representation.ClassFunction G)
    (hchi : Representation.IsIrreducibleCharacter chi)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime P) G)) :
    Localization.AtPrime P :=
  ∑ c : ConjClasses G,
    centralClassCoefficient z c *
      algebraMap (Representation.cyclotomicOrder eta)
        (Localization.AtPrime P)
        (centralCharacterInCyclotomicOrder heta chi hchi c)

/-- Any linear combination over the localization of the defining
central-character congruences remains in the maximal ideal. -/
theorem centralCharacterLinearCombination_sub_mem_maximalIdeal
    {eta : ℂ} (heta : IsPrimitiveRoot eta (Nat.card G))
    (P : Ideal (Representation.cyclotomicOrder eta)) [P.IsPrime]
    (chi psi : Representation.ClassFunction G)
    (hchi : Representation.IsIrreducibleCharacter chi)
    (hpsi : Representation.IsIrreducibleCharacter psi)
    (hsame : SameTwoBlock heta P chi psi hchi hpsi)
    (a : ConjClasses G → Localization.AtPrime P) :
    (∑ c : ConjClasses G,
        a c * algebraMap (Representation.cyclotomicOrder eta)
          (Localization.AtPrime P)
          (centralCharacterInCyclotomicOrder heta chi hchi c)) -
      (∑ c : ConjClasses G,
        a c * algebraMap (Representation.cyclotomicOrder eta)
          (Localization.AtPrime P)
          (centralCharacterInCyclotomicOrder heta psi hpsi c)) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  classical
  rw [← Finset.sum_sub_distrib]
  apply Ideal.sum_mem
  intro c _hc
  rw [← mul_sub, ← map_sub]
  apply Ideal.mul_mem_left
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime P) P _).2
      ((sameTwoBlock_iff heta P chi psi hchi hpsi).mp hsame c)

/-- A central localized group-algebra element has congruent scalars on any
two irreducible characters in the same ordinary congruence block. -/
theorem localizedCentralScalar_sub_mem_maximalIdeal
    {eta : ℂ} (heta : IsPrimitiveRoot eta (Nat.card G))
    (P : Ideal (Representation.cyclotomicOrder eta)) [P.IsPrime]
    (chi psi : Representation.ClassFunction G)
    (hchi : Representation.IsIrreducibleCharacter chi)
    (hpsi : Representation.IsIrreducibleCharacter psi)
    (hsame : SameTwoBlock heta P chi psi hchi hpsi)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime P) G)) :
    localizedCentralScalar heta P chi hchi z -
        localizedCentralScalar heta P psi hpsi z ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  exact centralCharacterLinearCombination_sub_mem_maximalIdeal
    heta P chi psi hchi hpsi hsame (centralClassCoefficient z)

/-- Equivalent residue-field formulation of the scalar congruence. -/
theorem residue_localizedCentralScalar_eq
    {eta : ℂ} (heta : IsPrimitiveRoot eta (Nat.card G))
    (P : Ideal (Representation.cyclotomicOrder eta)) [P.IsPrime]
    (chi psi : Representation.ClassFunction G)
    (hchi : Representation.IsIrreducibleCharacter chi)
    (hpsi : Representation.IsIrreducibleCharacter psi)
    (hsame : SameTwoBlock heta P chi psi hchi hpsi)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime P) G)) :
    IsLocalRing.residue (Localization.AtPrime P)
        (localizedCentralScalar heta P chi hchi z) =
      IsLocalRing.residue (Localization.AtPrime P)
        (localizedCentralScalar heta P psi hpsi z) := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact localizedCentralScalar_sub_mem_maximalIdeal
    heta P chi psi hchi hpsi hsame z

end CentralScalarCongruence

end Submission.ZStar
