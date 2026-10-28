module

public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.PerfectCentralSupplement
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# Local bounds on perfect central kernels

Let `E → G` be a finite perfect central cover and let `H ≤ E` map onto
`P ≤ G`, where `[G : P]` is prime to `p`. Transfer puts every central
`p`-subgroup in the derived subgroup of the full preimage of `P`. Changing
commutator arguments by central kernel elements shows that this derived
subgroup lies in `H`. Thus every `p`-power divisor of the global kernel
order is at most the order of `H ∩ ker(E → G)`.

This allows a local lift with a small kernel, rather than requiring a
section. The application to the exceptional G₂(3) multiplier is in
`Theory.SpecificGroups.G2.MultiplierThree.UpperBound`.
Source: the central transfer argument underlying Aschbacher–Smith I.1.2,
printed p.407 (PDF p.418), and the multiplier calculations in GLS3 §6.1.
-/

namespace PerfectCentralCovering
open Subgroup
open scoped commutatorElement

variable {E G : Type*} [Group E] [Group G]

/-- A subgroup surjecting onto `P` contains the derived subgroup of its
full preimage under a central extension. -/
public theorem commutator_preimage_le_of_map_eq
    (f : E →* G) (hc : f.ker ≤ center E)
    (H : Subgroup E) (P : Subgroup G) (hmap : H.map f = P) :
    ⁅P.comap f, P.comap f⁆ ≤ H := by
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hx)
  obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hy)
  rw [CentralExtension.commutator_eq_of_image_eq f hc hax.symm hby.symm]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

/-- Transfer detects every central `p`-subgroup in any lift of a subgroup
of index prime to `p`. -/
public theorem Cover.central_pSubgroup_le_local_lift [Finite E]
    (f : Cover E G) {p : ℕ} [Fact p.Prime]
    (H : Subgroup E) (P : Subgroup G) (hmap : H.map f.toMonoidHom = P)
    (hi : ¬ p ∣ P.index) (K : Subgroup E)
    (hK : K ≤ f.toMonoidHom.ker) (hKp : IsPGroup p K) : K ≤ H := by
  let : Group.IsPerfect E := f.isPerfect
  have hpre : K ≤ P.comap f.toMonoidHom := by
    intro x hx
    change f.toMonoidHom x ∈ P
    rw [MonoidHom.mem_ker.mp (hK hx)]
    exact P.one_mem
  have hi' : ¬ p ∣ (P.comap f.toMonoidHom).index := by
    rwa [P.index_comap_of_surjective f.surjective]
  exact (central_pSubgroup_le_commutator _ K hpre
    (hK.trans f.ker_le_center) hKp hi').trans
    (commutator_preimage_le_of_map_eq f.toMonoidHom f.ker_le_center H P hmap)

/-- Every `p`-power divisor of the global kernel order divides the kernel
order of any local lift over a subgroup of index prime to `p`. -/
public theorem Cover.primePower_dvd_local_kernel_card [Finite E]
    (f : Cover E G) {p : ℕ} [Fact p.Prime]
    (H : Subgroup E) (P : Subgroup G) (hmap : H.map f.toMonoidHom = P)
    (hi : ¬ p ∣ P.index) {n : ℕ} (hd : p ^ n ∣ Nat.card f.toMonoidHom.ker) :
    p ^ n ∣ Nat.card (H ⊓ f.toMonoidHom.ker : Subgroup E) := by
  obtain ⟨Z, hZ⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := f.toMonoidHom.ker) p hd
  let K := Z.map f.toMonoidHom.ker.subtype
  have hK : K ≤ f.toMonoidHom.ker := by
    rintro x ⟨z, _, rfl⟩
    exact z.property
  have hKp : IsPGroup p K := (IsPGroup.of_card hZ).map f.toMonoidHom.ker.subtype
  have hKH : K ≤ H := f.central_pSubgroup_le_local_lift H P hmap hi K hK hKp
  have hcard : Nat.card K = p ^ n := by
    rw [Subgroup.card_map_of_injective f.toMonoidHom.ker.subtype_injective]
    exact hZ
  rw [← hcard]
  exact Subgroup.card_dvd_of_le (le_inf hKH hK)

/-- A `p`-power dividing the global kernel order is bounded by the kernel
of any local lift over a subgroup of index prime to `p`. -/
public theorem Cover.primePower_le_local_kernel_card [Finite E]
    (f : Cover E G) {p : ℕ} [Fact p.Prime]
    (H : Subgroup E) (P : Subgroup G) (hmap : H.map f.toMonoidHom = P)
    (hi : ¬ p ∣ P.index) {n : ℕ} (hd : p ^ n ∣ Nat.card f.toMonoidHom.ker) :
    p ^ n ≤ Nat.card (H ⊓ f.toMonoidHom.ker : Subgroup E) :=
  Nat.le_of_dvd Nat.card_pos (f.primePower_dvd_local_kernel_card H P hmap hi hd)

/-- A local lift whose kernel has order prime to `p` removes `p` from
the global perfect central kernel. Other primes in the local kernel are allowed. -/
public theorem Cover.not_dvd_kernel_of_local_lift [Finite E]
    (f : Cover E G) {p : ℕ} [Fact p.Prime]
    (H : Subgroup E) (P : Subgroup G) (hmap : H.map f.toMonoidHom = P)
    (hi : ¬ p ∣ P.index) (hlocal : ¬ p ∣ Nat.card (H ⊓ f.toMonoidHom.ker : Subgroup E)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  intro hd
  apply hlocal
  simpa using f.primePower_dvd_local_kernel_card H P hmap hi (n := 1) (by simpa using hd)

/-- A strict bound on a local lift's kernel excludes the same `p`-power
from the full perfect central kernel. -/
public theorem Cover.not_primePower_dvd_kernel_of_local_bound [Finite E]
    (f : Cover E G) {p : ℕ} [Fact p.Prime]
    (H : Subgroup E) (P : Subgroup G) (hmap : H.map f.toMonoidHom = P)
    (hi : ¬ p ∣ P.index) {n : ℕ}
    (hb : Nat.card (H ⊓ f.toMonoidHom.ker : Subgroup E) < p ^ n) :
    ¬ p ^ n ∣ Nat.card f.toMonoidHom.ker :=
  fun hd => (Nat.not_le_of_gt hb) (f.primePower_le_local_kernel_card H P hmap hi hd)

end PerfectCentralCovering
