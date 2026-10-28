module
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.SpecificGroups.Alternating.SevenSolvableOvergroups
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Alternating-six sections in a group with alternating-seven socle

A subgroup of A₇ with A₆ two-core quotient has trivial two-core: its core
order is a power of two dividing seven. A two-subgroup centralizing that
section therefore centralizes the subgroup itself. The actual conjugation
embedding of a group with F*=A₇ into S₇ reduces this to the involution
centralizer orders48 and240, neither divisible by nine.

The commutator hypothesis uses the embedded two-core of the original
subgroup, so the result applies to an actual quotient-action centralizer.
Source application: Aschbacher--Smith12.6.14, printed p.826, combined
manuscript of1 March2004.
-/

public section
open Subgroup Equiv Theory.GroupTheory
open scoped commutatorElement
namespace Theory.SpecificGroups.SymmetricSeven

/-- No involution centralizer in S₇ has a factor nine. -/
theorem involution_centralizer_not_nine (z : Perm (Fin 7)) (hz : orderOf z = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({z} : Set (Perm (Fin 7)))) := by
  have hp : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have ht := Perm.cycleType_of_pow_prime_eq_one hp
  have hs := z.sum_cycleType_le
  rw [ht,Multiset.sum_replicate] at hs
  have hpos : 0 < z.cycleType.card := by
    apply Nat.pos_of_ne_zero
    intro h
    have he : z = 1 := Perm.cycleType_eq_zero.mp (Multiset.card_eq_zero.mp h)
    simp [he] at hz
  have hb : z.cycleType.card ≤ 3 := by
    simp only [nsmul_eq_mul,Nat.cast_id,Fintype.card_fin] at hs
    omega
  have hcases : z.cycleType.card = 1 ∨ z.cycleType.card = 2 ∨ z.cycleType.card = 3 := by omega
  rw [Perm.nat_card_centralizer,ht]
  rcases hcases with h | h | h <;> rw [h] <;> norm_num [Nat.factorial]

/-- A two-subgroup centralizing a subgroup with a factor nine in S₇ is trivial. -/
theorem two_centralizer_eq_bot (B R : Subgroup (Perm (Fin 7)))
    (hB : 9 ∣ Nat.card B) (hR : IsPGroup 2 R)
    (hc : R ≤ centralizer (B : Set (Perm (Fin 7)))) : R = ⊥ := by
  by_contra hn
  have hcard : Nat.card R ≠ 1 := fun h => hn (card_eq_one.mp h)
  obtain ⟨n,hn⟩ := hR.exists_card_eq
  have hn0 : n ≠ 0 := by intro he; exact hcard (hn.trans (by simp [he]))
  have hd : 2 ∣ Nat.card R := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨r,hr⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 hd
  have hBC : B ≤ centralizer ({(r : Perm (Fin 7))} : Set (Perm (Fin 7))) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr ((hc r.property) b hb)
  exact involution_centralizer_not_nine r ((Subgroup.orderOf_coe r).trans hr)
    (hB.trans (card_dvd_of_le hBC))

end Theory.SpecificGroups.SymmetricSeven
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A local A₆ section in an A₇ socle has no nontrivial two-group section centralizer. -/
theorem seven_socle_two_section_centralizer
    (K A R : Subgroup G) (hK : K = generalizedFitting G)
    (eK : K ≃* alternatingGroup (Fin 7)) (hAK : A ≤ K)
    (eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (hR : IsPGroup 2 R) (hRA : ⁅R,A⁆ ≤ A.pCoreIn 2) : R = ⊥ := by
  have hAc : Nat.card (A ⧸ pCore 2 A) = 360 := by
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hAcard : Nat.card A = 360 * Nat.card (pCore 2 A) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A),hAc]
  have hd : Nat.card (pCore 2 A) ∣ 7 := by
    have hh := card_dvd_of_le hAK
    rw [Nat.card_congr eK.toEquiv,nat_card_alternatingGroup,hAcard] at hh
    norm_num [Nat.factorial] at hh
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 360) hh
  have hcore : pCore 2 A = ⊥ := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
    have hn0 : n = 0 := by
      by_contra h
      have htwo : 2 ∣ 7 := (dvd_pow_self 2 h).trans (hn ▸ hd)
      norm_num at htwo
    exact card_eq_one.mp (by simpa [hn0] using hn)
  have hC : R ≤ centralizer (A : Set G) := by
    intro r hr
    apply mem_centralizer_iff.mpr
    intro a ha
    have hh := hRA (commutator_mem_commutator hr ha)
    change ⁅r,a⁆ ∈ (pCore 2 A).map A.subtype at hh
    rw [hcore,Subgroup.map_bot,mem_bot] at hh
    exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
  obtain ⟨f,hf,_⟩ := alternatingGroup.SevenSolvableGeneration.exists_socle_embedding K hK eK
  have hcard : 9 ∣ Nat.card (A.map f) := by
    rw [card_map_of_injective hf,hAcard]
    exact dvd_mul_of_dvd_left (by decide : 9 ∣ 360) _
  have hc : R.map f ≤ centralizer (A.map f : Set (Perm (Fin 7))) := by
    rintro _ ⟨r,hr,rfl⟩ _ ⟨a,ha,rfl⟩
    simpa only [map_mul] using congrArg f (hC hr a ha)
  have hz := Theory.SpecificGroups.SymmetricSeven.two_centralizer_eq_bot
    (A.map f) (R.map f) hcard (hR.map f) hc
  apply bot_unique
  intro r hr
  have hh : f r = 1 := by
    have hm := mem_map_of_mem f hr
    rwa [hz,mem_bot] at hm
  exact hf (hh.trans f.map_one.symm)
end Theory.GroupTheory
