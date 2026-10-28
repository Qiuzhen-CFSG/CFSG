module

public import Theory.GroupTheory.ChiefFactorDirectPower
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Solvable
public import Mathlib.RingTheory.IntegralDomain

/-!
# Cyclic composition factors of solvable groups

An explicit simple section inherits solvability from its actual subgroup
quotient. A simple solvable group is abelian, hence cyclic of prime order.
Its automorphism group is identified with the units of the corresponding
prime field, so is cyclic as well.

The section kernel is normal only in its section subgroup; no ambient
normality is assumed. This supplies the cyclic-factor input to
Aschbacher--Smith, *The Classification of Quasithin Groups*, E.1.13, p.214.
-/

public section
open scoped IsMulCommutative
namespace ChiefFactor.SimpleSection
variable {G S : Type*} [Group G] [Group S] [Group.IsSolvable G]

theorem isSolvable (s : ChiefFactor.SimpleSection G S) : Group.IsSolvable S := by
  let _ := s.normal
  exact Group.isSolvable_of_surjective (f := s.equiv.toMonoidHom) s.equiv.surjective

theorem isCyclic (s : ChiefFactor.SimpleSection G S) : IsCyclic S := by
  let _ := s.simple
  let _ := s.isSolvable
  let _ : IsMulCommutative S := ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance⟩⟩
  infer_instance

theorem prime_card (s : ChiefFactor.SimpleSection G S) : (Nat.card S).Prime := by
  let _ := s.simple
  let _ := s.isCyclic
  exact IsSimpleGroup.prime_card

/-- The full automorphism group of an actual solvable simple section is cyclic. -/
theorem automorphism_isCyclic (s : ChiefFactor.SimpleSection G S) : IsCyclic (MulAut S) := by
  let _ := s.isCyclic
  let _ : Fact (Nat.card S).Prime := ⟨s.prime_card⟩
  exact isCyclic_of_injective (IsCyclic.mulAutMulEquiv S).toMonoidHom
    (IsCyclic.mulAutMulEquiv S).injective
end ChiefFactor.SimpleSection
