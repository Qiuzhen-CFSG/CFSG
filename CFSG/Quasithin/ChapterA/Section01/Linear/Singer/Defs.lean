module

public import Theory.LinearAlgebra.RegularLinearAction
public import Mathlib.GroupTheory.PGroup

/-!
# The shared fixed-vector input for A.1.12

Aschbacher–Smith A.1.12, printed p.22, uses Aschbacher, *Finite Group
Theory*, 36.2 in both its primitive-prime and dimension-six branches.
For an odd linear group, its contrapositive says that a fixed-point-free
prime-order element centralizes each normal q-subgroup with a different
prime q. Normality here is inside the given linear subgroup Y.

The proposition below specifies that shared representation-theoretic input.
It is not an assumption in a completed A.1.12 theorem: final assembly must
prove it from oddness. In particular, it contains no Singer-normality clause.
The underlying regularity predicate is the actual action on nonzero vectors
in `Theory.LinearAlgebra.RegularLinearAction`.
-/

namespace CFSG.Quasithin.ChapterA.Singer

/-- The fixed-vector theorem in precisely the form used on normal prime-power
subgroups of the odd overgroup. All commutation takes place in the actual Y. -/
@[expose] public def PrimeFixedPointCentralization
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (Y : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ q r : ℕ, q.Prime → r.Prime → q ≠ r →
    ∀ N : Subgroup Y, N.Normal → IsPGroup q N →
      ∀ x : Y, orderOf x = r →
        (∀ v : V, (x : V ≃ₗ[ZMod 2] V) v = v → v = 0) →
          ∀ a : N, Commute x (a : Y)

end CFSG.Quasithin.ChapterA.Singer
