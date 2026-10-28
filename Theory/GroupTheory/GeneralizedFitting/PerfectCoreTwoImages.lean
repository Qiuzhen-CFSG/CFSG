module
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import Theory.Quasithin.CoprimeRank

/-!
# Solvable kernels in perfect simple two-core extensions

The solvable radical is the two-core. Consequently every solvable
homomorphism kernel is a two-group, and odd-prime ranks survive the map.
The actual A₆ residual in the C.2.7 star quotient is a consumer.

Source: standard radical and coprime-rank calculus used in
Aschbacher–Smith 3.3.22, p.597.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.PerfectCoreTwoExtension
variable {B D : Type*} [Group B] [Finite B] [Group D] [Finite D] [Group.IsPerfect B]
  [IsSimpleGroup (B ⧸ pCore 2 B)]

omit [Finite D] in
/-- Every solvable homomorphism kernel is contained in the actual two-core. -/
theorem solvable_ker_le_core (f : B →* D) [Group.IsSolvable f.ker] : f.ker ≤ pCore 2 B := by
  rw [←radical_eq_core]
  exact le_solvableRadical _ inferInstance inferInstance

/-- An odd prime rank survives a solvable kernel for a perfect simple two-core extension. -/
theorem odd_rank_le_of_solvable_kernel {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (f : B →* D) [Group.IsSolvable f.ker] : primeRank p B ≤ primeRank p D := by
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.to_le (solvable_ker_le_core f)
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  exact primeRank_le_of_coprime_ker p f (by rw [hn]; exact hp.coprime_two_right.pow_right n)

end Theory.GroupTheory.PerfectCoreTwoExtension
