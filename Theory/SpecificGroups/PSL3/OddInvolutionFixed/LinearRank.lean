module
public import GorensteinWalter.PSL2CoprimeSylowCyclic
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.LinearAlgebra.SpecialLinearDeterminantKernel

/-!
# Derived three-rank in quotients of GL₂ over odd prime fields

When the field prime is different from three, the Sylow three-subgroups of
SL₂ are cyclic. The central projection preserves these Sylow groups because
its kernel has order dividing two. For PSL₂ we use the proved cyclic-torus
calculation, treating the five-element field by its exact order.

For any surjection from GL₂, its target's commutator subgroup lies in the
image of the determinant kernel SL₂. Cyclic Sylow subgroups survive a
surjection, so this image, and hence the derived subgroup, has three-rank at
most one. No general quotient monotonicity of prime rank is assumed.

Source: Huppert II.8.2–5 and the inner-involution inspection in
Aschbacher–Smith E.6.18, printed p.252 (PDF p.263).
-/

public section
open scoped MatrixGroups
open Subgroup
namespace Matrix.PSL3.OddInvolutionFixed
variable {F : Type*} [Field F] [Finite F]

theorem sl2_sylow_three_isCyclic {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hp3 : p ≠ 3) (hF : Nat.card F = p) (P : Sylow 3 SL(2,F)) : IsCyclic P := by
  let : Fact p.Prime := ⟨hp⟩
  let Q : Sylow 3 PSL(2,F) := default
  have hQ : IsCyclic Q := by
    by_cases h7 : 7 ≤ p
    · exact GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F
        (by simpa using hF : Nat.card F = p ^ 1) (hF ▸ h7) 3 (by decide)
        (by rw [hF]; exact (Nat.coprime_primes (by decide) hp).mpr (Ne.symm hp3)) Q
    · have hp5 : p = 5 := by
        have hp2 := hp.two_le
        have hpodd : p % 2 = 1 := Nat.odd_iff.mp ho
        omega
      have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho)
      rw [hF, hp5] at hc
      have hcard : Nat.card PSL(2,F) = 60 := by omega
      apply isCyclic_of_prime_card (p := 3)
      rw [Q.card_eq_multiplicity, hcard]
      decide +kernel
  let q : SL(2,F) →* PSL(2,F) := QuotientGroup.mk' (center SL(2,F))
  have hk : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [show q.ker = center SL(2,F) from QuotientGroup.ker_mk' _,
      Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
    exact (by decide : Nat.Coprime 3 2).of_dvd_right (Nat.gcd_dvd_left 2 _)
  exact (P.equivOfSurjectiveCoprime q (QuotientGroup.mk'_surjective _) hk Q).isCyclic.mpr hQ

theorem derived_rank_of_gl2_surjective {H : Type*} [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) (hF : Nat.card F = p)
    (f : GL (Fin 2) F →* H) (hf : Function.Surjective f) :
    primeRank 3 (commutator H) ≤ 1 := by
  let D := (GeneralLinearGroup.det (n := Fin 2) (R := F)).ker
  have hD : commutator H ≤ D.map f := by
    have he : (commutator (GL (Fin 2) F)).map f = commutator H := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
      rfl
    rw [← he]
    exact map_mono (Abelianization.commutator_subset_ker _)
  let e := SpecialLinearGroup.determinantKernelEquiv (Fin 2) F
  let q : SL(2,F) →* D.map f := (f.subgroupMap D).comp e.toMonoidHom
  have hq : Function.Surjective q := (f.subgroupMap_surjective D).comp e.surjective
  let P : Sylow 3 SL(2,F) := default
  have hr := P.primeRank_le_one_of_surjective (sl2_sylow_three_isCyclic hp ho hp3 hF P) q hq
  exact (primeRank_mono 3 hD).trans hr

end Matrix.PSL3.OddInvolutionFixed
