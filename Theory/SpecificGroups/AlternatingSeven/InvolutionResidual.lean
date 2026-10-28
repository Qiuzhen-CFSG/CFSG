module
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry.Coordinates
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The marked cubic in a seven-point involution centralizer

The centralizer of (01)(23) in S₇ is the product of its standard Sylow
two-subgroup and the cyclic group on {4,5,6}. Consequently a nontrivial
two-perfect subgroup centralizing an even involution is precisely that
cubic group after one simultaneous relabelling. The calculation uses only
the sixteen Sylow words and the centralizer order formula.

This supplies the original L₁ image marking in the cubic A₇-cover branch
of Aschbacher–Smith, proof of 12.6.26, printed p.832.
-/

public section
open Equiv Subgroup
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
namespace AlternatingSeven.InvolutionResidual
private abbrev doubleSwap : S7 := swap01 * swap23
private abbrev tailCycle : S7 := swap 4 5 * swap 5 6
private theorem tail_order : orderOf tailCycle = 3 := by
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
private theorem sylow_normalizes_tail : sylowTwo ≤ normalizer (zpowers tailCycle : Set S7) := by
  rintro _ ⟨w,rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  rcases (by decide +kernel : ∀ w : Quadruple,
    word w * tailCycle * (word w)⁻¹ = tailCycle ∨
    word w * tailCycle * (word w)⁻¹ = tailCycle⁻¹) w with h|h
  · change zpowers (word w * tailCycle * (word w)⁻¹) = _
    rw [h]
  · change zpowers (word w * tailCycle * (word w)⁻¹) = _
    rw [h,zpowers_inv]
private theorem standard_centralizer :
    centralizer ({doubleSwap} : Set S7) = zpowers tailCycle ⊔ sylowTwo := by
  have h2 : IsPGroup 2 sylowTwo := IsPGroup.of_card (show Nat.card sylowTwo = 2^4 by
    rw [sylowTwo_card]; decide)
  have h3 : IsPGroup 3 (zpowers tailCycle) := IsPGroup.of_card (show Nat.card (zpowers tailCycle) = 3^1 by
    rw [Nat.card_zpowers,tail_order]; decide)
  have hle : zpowers tailCycle ⊔ sylowTwo ≤ centralizer ({doubleSwap} : Set S7) := by
    apply sup_le
    · apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr (by decide +kernel)
    · rintro _ ⟨w,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      exact (by decide +kernel : ∀ w : Quadruple, word w * doubleSwap = doubleSwap * word w) w
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ sylow_normalizes_tail
    (h3.disjoint_of_coprime h2 (by decide)),Nat.card_zpowers,tail_order,sylowTwo_card]
  rw [Perm.nat_card_centralizer,show doubleSwap.cycleType = {2,2} from by decide +kernel]
  norm_num [Nat.factorial]
private theorem conjugate_involution (z : S7) (hz : z ∈ alternatingGroup (Fin 7))
    (ho : orderOf z = 2) : ∃ g : S7, g*z*g⁻¹ = doubleSwap := by
  obtain ⟨n,hn⟩ := Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hn
  have hs := z.sum_cycleType_le
  rw [hn,Multiset.sum_replicate] at hs
  have hnle : n ≤ 2 := by simp only [Fintype.card_fin,smul_eq_mul] at hs; omega
  have he : Perm.sign z = 1 := hz
  rw [Perm.sign_of_cycleType,hn] at he
  have heint := congrArg (fun u : ℤˣ => (u : ℤ)) he
  have hn1 : n = 1 := by
    interval_cases n
    · norm_num at heint
    · rfl
    · norm_num at heint
  subst n
  apply isConj_iff.mp
  apply Perm.isConj_iff_cycleType_eq.mpr
  rw [hn]
  decide +kernel

/-- A nontrivial two-perfect subgroup centralizing an even involution on seven
letters is the cubic group on its three fixed letters, with one simultaneous relabelling. -/
theorem marked_cubic (A : Subgroup S7) (hA : IsPPerfect 2 A) (hne : A ≠ ⊥)
    (z : S7) (hz : z ∈ alternatingGroup (Fin 7)) (ho : orderOf z = 2)
    (hc : A ≤ centralizer ({z} : Set S7)) :
    ∃ g : S7, g*z*g⁻¹ = swap01*swap23 ∧
      A.map (MulAut.conj g).toMonoidHom = zpowers (swap 4 5 * swap 5 6) := by
  obtain ⟨g,hg⟩ := conjugate_involution z hz ho
  let e := MulAut.conj g
  let B := A.map e.toMonoidHom
  have hp : IsPPerfect 2 B := hA.of_surjective (e.toMonoidHom.subgroupMap A)
    (MonoidHom.subgroupMap_surjective _ _)
  have hBC : B ≤ centralizer ({doubleSwap} : Set S7) := by
    rintro _ ⟨a,ha,rfl⟩
    have hh := congrArg e (mem_centralizer_singleton_iff.mp (hc ha))
    have hez : e z = doubleSwap := hg
    apply mem_centralizer_singleton_iff.mpr
    change e a * doubleSwap = doubleSwap * e a
    simpa only [map_mul,hez] using hh
  have hBT : B ≤ zpowers tailCycle := B.le_of_isPPerfect_of_le_sup_of_normalizes
    _ _ hp (IsPGroup.of_card (show Nat.card sylowTwo = 2^4 by rw [sylowTwo_card]; decide))
      sylow_normalizes_tail (hBC.trans_eq standard_centralizer)
  have hb : B ≠ ⊥ := by
    intro hh
    exact hne ((A.map_eq_bot_iff_of_injective e.injective).mp hh)
  have hd : Nat.card B ∣ 3 := by
    simpa only [Nat.card_zpowers,tail_order] using card_dvd_of_le hBT
  have hcard : Nat.card B = 3 := (Nat.prime_three.eq_one_or_self_of_dvd _ hd).resolve_left
    (fun h => hb (card_eq_one.mp h))
  refine ⟨g,hg,eq_of_le_of_card_ge hBT ?_⟩
  rw [Nat.card_zpowers,tail_order,hcard]

end AlternatingSeven.InvolutionResidual
