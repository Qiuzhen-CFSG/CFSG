module

public import Theory.Representation.FreeBasis
public import Mathlib.Algebra.DirectSum.Module

/-!
# Freeness from free equivariant orbit bases

A basis transported by a representation action along a free group action is a
basis of a free representation.  The proof reindexes the basis by orbit
representatives and the group coordinate, identifies the resulting
representation with `Representation.free`, and transfers the canonical
MonoidAlgebra-module basis.  The orbit specialization uses
`MulAction.selfEquivOrbitsQuotientProd`; no characteristic hypothesis occurs.
-/

noncomputable section
namespace Representation

attribute [local instance] Classical.decEq

public theorem free_of_equivariant_basis
    {E A V I α : Type*} [Field E] [Group A] [Finite A]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Finite I] [Finite α] [MulAction A I]
    (rho : Representation E A V) (b : Module.Basis I E V)
    (q : I ≃ α × A)
    (hq : ∀ a i, q (a • i) = ((q i).1, a * (q i).2))
    (htransport : ∀ a i, rho a (b i) = b (a • i)) :
    Module.Free (MonoidAlgebra E A) rho.asModule := by
  classical
  let target : Representation E A (α →₀ MonoidAlgebra E A) :=
    Representation.free E A α
  let targetBasis : Module.Basis (α × A) E (target.asModule) :=
    Representation.freeBasis E A α
  let eLin : V ≃ₗ[E] (target.asModule) :=
    (b.equiv targetBasis q)
  have he : rho ≃ₗ target := by
    refine Representation.RepEquiv.mk eLin ?_
    intro a
    apply b.ext
    intro i
    change eLin (rho a (b i)) = target a (eLin (b i))
    rw [htransport]
    simp only [eLin, Module.Basis.equiv_apply, LinearEquiv.symm_apply_apply]
    change targetBasis (q (a • i)) = target a (targetBasis (q i))
    rw [hq]
    change (Representation.freeBasis E A α) ((q i).1, a * (q i).2) =
      (Representation.free E A α) a ((Representation.freeBasis E A α) (q i))
    exact (Representation.free_apply_freeBasis_pair E A α a (q i).2 (q i).1).symm
  let em := RepMap.equivLinearMapAsModule rho target he.toRepMap
  exact Module.Free.of_equiv' (free_asModule_free E A α)
    (LinearEquiv.ofBijective em ⟨he.toLinearEquiv.injective, he.toLinearEquiv.surjective⟩).symm

public theorem free_of_free_orbit_basis
    {E A V I : Type*} [Field E] [Group A] [Finite A]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Finite I] [MulAction A I]
    (rho : Representation E A V) (b : Module.Basis I E V)
    (htransport : ∀ a i, rho a (b i) = b (a • i))
    (hfree : ∀ i, MulAction.stabilizer A i = ⊥)
    (horbit : ∀ (a : A) (i : I),
      MulAction.selfEquivOrbitsQuotientProd hfree (a • i) =
        ((MulAction.selfEquivOrbitsQuotientProd hfree i).1,
          a * (MulAction.selfEquivOrbitsQuotientProd hfree i).2)) :
    Module.Free (MonoidAlgebra E A) rho.asModule := by
  let alpha := Quotient (MulAction.orbitRel A I)
  let orbitEquiv : I ≃ alpha × A :=
    MulAction.selfEquivOrbitsQuotientProd hfree
  exact free_of_equivariant_basis rho b orbitEquiv (by
    intro a i
    exact horbit a i) htransport

end Representation
