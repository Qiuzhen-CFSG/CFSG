module
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# Comparing residuals through a two-group kernel

The prime-to-three residual always lies in the two-residual. If the two
residuals agree in a homomorphic image with two-group kernel, they agree
upstairs: the two-perfect residual cannot acquire a nontrivial two-group
quotient over the normal cubic residual.

This retains the literal homomorphism and its kernel. The source application
is the lift from a Sylow overgroup in A₈ to C_L(Ω₁Z(T)) in Aschbacher–Smith,
3.3.21(e), printed p.596 of the combined manuscript (1 March 2004).
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Finite G] [Group H]

theorem primeToResidual_three_le_twoResidual : primeToResidual 3 G ≤ pResidual 2 G := by
  apply primeToResidual_le
  obtain ⟨n, hn⟩ := (isPGroup_quotient_pResidual (G := G) 2).exists_card_eq
  change Nat.Coprime 3 (Nat.card (G ⧸ pResidual 2 G))
  rw [hn]
  exact (by decide : Nat.Coprime 3 2).pow_right n

theorem twoResidual_eq_primeToResidual_three_of_two_kernel (f : G →* H) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hH : pResidual 2 H = primeToResidual 3 H) :
    pResidual 2 G = primeToResidual 3 G := by
  apply le_antisymm _ primeToResidual_three_le_twoResidual
  apply isPPerfect_le_of_map_le_of_kernel_normalizes f _ _ (isPPerfect_pResidual 2)
    hk le_normalizer_of_normal
  rw [map_pResidual_of_surjective 2 f hf, map_primeToResidual_of_surjective 3 f hf, hH]

end Subgroup
