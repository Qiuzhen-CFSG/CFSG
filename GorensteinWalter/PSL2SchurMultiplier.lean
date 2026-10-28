module

public import GorensteinWalter.PSL2EvenDefiningKernel
public import GorensteinWalter.PSL2OddDefiningKernel

/-!
# Universal PSL₂ covers outside the exceptional orders

For every finite field of odd order greater than three, other than order
nine, the actual projection SL₂(F) → PSL₂(F) is universal. The defining-prime
exclusion completes the cyclic-torus and dihedral-Sylow kernel bounds;
order five uses the already proved prime-field argument.

For even order at least eight the identity cover is universal, as proved
in `PSL2EvenDefiningKernel`. Its kernel is explicitly equivalent to the
trivial group. Together with the odd projection-kernel equivalence and the
separate order-four double cover, these give the PSL₂ multiplier entries.
Order nine is excluded because its multiplier has an exceptional three-part.

Source: Aschbacher–Smith, I.1.3(1),(3) and I.1.4(1), printed pp.407–408,
citing GLS III, Section 6.1, Tables 6.1.2–6.1.3.
-/

open Theory.GroupTheory
open scoped MatrixGroups

namespace GorensteinWalter.PSL2Cover

universe u w
variable (F : Type u) [Field F] [Finite F] [Fact (3 < Nat.card F)]

/-- The canonical SL₂ projection is universal for odd q > 3, q ≠ 9,
with the defining-characteristic premise fully discharged. -/
public theorem isUniversal_of_odd (ho : Odd (Nat.card F)) (h9 : Nat.card F ≠ 9) :
    Covering.IsUniversal.{u, u, w} (cover F) := by
  by_cases h5 : Nat.card F = 5
  · exact isUniversal_of_card_prime F (h5 ▸ (by decide : Nat.Prime 5))
  · have hF : 7 ≤ Nat.card F := by
      have := Fact.out (p := 3 < Nat.card F)
      obtain ⟨k, hk⟩ := ho
      omega
    exact isUniversal_of_defining_prime_not_dvd F ho hF
      (defining_prime_not_dvd_universal_kernel F ho Fact.out h9)

/-- The identity covering has trivial kernel. Its universality for even
q ≥ 8 makes this the Schur-multiplier calculation in that range. -/
public def identityKernelEquivOne :
    (Covering.id : Covering PSL(2, F) PSL(2, F)).toMonoidHom.ker ≃* PUnit := by
  letI : Subsingleton
      (Covering.id : Covering PSL(2, F) PSL(2, F)).toMonoidHom.ker := by
    change Subsingleton (MonoidHom.id PSL(2, F)).ker
    rw [MonoidHom.ker_id]
    infer_instance
  letI : Unique
      (Covering.id : Covering PSL(2, F) PSL(2, F)).toMonoidHom.ker := uniqueOfSubsingleton 1
  exact MulEquiv.ofUnique

end GorensteinWalter.PSL2Cover
