module
public import Theory.GroupAction.Invariant
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-!
# Actions on small normal two-sections

A group of order dividing sixteen admits no automorphism of prime order
at least eleven. Orbit counting compares the order with the fixed subgroup;
the divisors 1, 2, 4, 8, 16 have distinct residues at every such prime.
For a relatively normal section, the literal conjugation action then turns
a theorem excluding homomorphisms into an ambient commutator containment.

Source application: Aschbacher--Smith 10.2.5, printed p.748. The common
kernel of the original two-core actions has index sixteen; the containing
odd-prime component cannot preserve this kernel. No normality in the
ambient simple group is assumed.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

/-- No prime at least eleven occurs in the automorphism group of a two-group
whose order divides sixteen. -/
theorem prime_not_dvd_aut_of_card_dvd_sixteen
    {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime) (hlarge : 11 ≤ p)
    (hd : Nat.card Q ∣ 16) : ¬ p ∣ Nat.card (MulAut Q) := by
  let : Fact p.Prime := ⟨hp⟩
  intro hdiv
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p hdiv
  let A := zpowers a
  have hA : IsPGroup p A := IsPGroup.of_card (n := 1) (by
    simpa only [A,Nat.card_zpowers,pow_one] using ha)
  let F := FixedPoints.subgroup A Q
  have hm := hA.card_modEq_card_fixedPoints Q
  change Nat.card Q % p = Nat.card F % p at hm
  have hq := Nat.mem_divisors.mpr ⟨hd,(by decide : (16:ℕ) ≠ 0)⟩
  have hf := Nat.mem_divisors.mpr ⟨F.card_subgroup_dvd_card.trans hd,(by decide : (16:ℕ) ≠ 0)⟩
  rw [show (16:ℕ).divisors = {1,2,4,8,16} by decide] at hq hf
  simp only [Finset.mem_insert,Finset.mem_singleton] at hq hf
  have hcases : p = 11 ∨ p = 13 ∨ 17 ≤ p := by
    have h2 := hp.eq_two_or_odd
    have h15 : p ≠ 15 := by rintro rfl; exact (by decide : ¬ Nat.Prime 15) hp
    omega
  have he : Nat.card F = Nat.card Q := by
    rcases hcases with rfl | rfl | hl
    · omega
    · omega
    · have hqbound : Nat.card Q < p := by omega
      have hfbound : Nat.card F < p := by omega
      rw [Nat.mod_eq_of_lt hqbound,Nat.mod_eq_of_lt hfbound] at hm
      exact hm.symm
  have ht := F.eq_top_of_card_eq he
  have hone : a = 1 := by
    apply MulEquiv.ext
    intro x
    exact (show x ∈ F from ht ▸ mem_top x) ⟨a,mem_zpowers a⟩
  rw [hone,orderOf_one] at ha
  omega

variable {G : Type*} [Group G] (K Q N : Subgroup G)
  [(N.subgroupOf Q).Normal]
  (hKQ : K ≤ normalizer (Q : Set G)) (hKN : K ≤ normalizer (N : Set G))

private def sectionAction : K →* MulAut (Q ⧸ N.subgroupOf Q) := by
  let a := Q.normalizerMonoidHom.comp (inclusion hKQ)
  have hn (k : K) : (N.subgroupOf Q).map (a k).toMonoidHom = N.subgroupOf Q := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (mem_normalizer_iff.mp (hKN k.property) x).mp hx
    · intro x hx
      refine ⟨(a k).symm x,?_,(a k).apply_symm_apply x⟩
      exact (mem_normalizer_iff.mp (hKN (K.inv_mem k.property)) x).mp hx
  exact {
    toFun k := QuotientGroup.congr _ _ (a k) (hn k)
    map_one' := by
      apply MulEquiv.ext
      intro x
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf Q) x
      change QuotientGroup.mk' _ (a 1 x) = QuotientGroup.mk' _ x
      rw [map_one]; rfl
    map_mul' := by
      intro k l
      apply MulEquiv.ext
      intro x
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf Q) x
      change QuotientGroup.mk' _ (a (k*l) x) = QuotientGroup.mk' _ (a k (a l x))
      rw [map_mul]; rfl }

include hKQ hKN in
/-- Triviality of every action on a preserved normal section forces the
literal ambient commutator into its denominator. -/
theorem commutator_le_of_section_hom_trivial
    (htriv : ∀ f : K →* MulAut (Q ⧸ N.subgroupOf Q), f = 1) : ⁅Q,K⁆ ≤ N := by
  have hh := htriv (sectionAction K Q N hKQ hKN)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro k hk q hq
  have he := congrArg (fun f : K →* MulAut (Q ⧸ N.subgroupOf Q) =>
    f ⟨k,hk⟩ (QuotientGroup.mk' _ ⟨q,hq⟩)) hh
  change QuotientGroup.mk' _ (Q.normalizerMonoidHom ⟨k,hKQ hk⟩ ⟨q,hq⟩) =
    QuotientGroup.mk' _ ⟨q,hq⟩ at he
  have hx := (QuotientGroup.eq_iff_div_mem).mp he
  change ((Q.normalizerMonoidHom ⟨k,hKQ hk⟩ ⟨q,hq⟩ : Q) : G) / q ∈ N at hx
  rw [normalizerMonoidHom_apply_apply_coe,div_eq_mul_inv] at hx
  exact hx
end Theory.GroupTheory
