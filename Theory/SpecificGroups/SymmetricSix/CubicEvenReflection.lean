module

public import Theory.SpecificGroups.SymmetricSix.CubicCentralizerOrder
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# An even reflection on a six-letter cubic centralizer

The common centralizer has order dividing both18 and16. Conjugation by the
involution makes its order even, so that order is exactly two. The calculation
uses cycle types and orbit congruence, without enumeration of permutation pairs.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix

private theorem even_involution_centralizer_card (r : Equiv.Perm (Fin 6))
    (hr : orderOf r = 2) (he : Equiv.Perm.sign r = 1) :
    Nat.card (centralizer ({r} : Set (Equiv.Perm (Fin 6)))) = 16 := by
  obtain ⟨n,hn⟩ := Equiv.Perm.cycleType_prime_order (hr ▸ Nat.prime_two)
  have hb := r.sum_cycleType_le
  rw [hn,hr,Multiset.sum_replicate] at hb
  norm_num [nsmul_eq_mul] at hb
  have hnle : n ≤ 2 := by omega
  have hs := Equiv.Perm.sign_of_cycleType r
  rw [he,hn,hr] at hs
  interval_cases n
  · norm_num at hs
  · rw [Equiv.Perm.nat_card_centralizer,hn,hr]
    norm_num
  · norm_num at hs

/-- An even involution inverting a cubic normalizes its full centralizer,
and its fixed subgroup there has order two. -/
theorem cubic_even_reflection_centralizer (t r : Equiv.Perm (Fin 6))
    (ht : orderOf t = 3) (hr : orderOf r = 2) (he : Equiv.Perm.sign r = 1)
    (hinv : r * t * r⁻¹ = t⁻¹) :
    r ∈ normalizer (centralizer ({t} : Set (Equiv.Perm (Fin 6))) : Set _) ∧
      Nat.card (centralizer ({t} : Set (Equiv.Perm (Fin 6))) ⊓
        centralizer ({r} : Set (Equiv.Perm (Fin 6))) : Subgroup _) = 2 := by
  have hn : r ∈ normalizer (zpowers t : Set (Equiv.Perm (Fin 6))) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers (r * t * r⁻¹) = zpowers t
    rw [hinv,zpowers_inv]
  have hnc := normalizer_le_normalizer_centralizer (zpowers t) hn
  simp only [zpowers_eq_closure,centralizer_closure] at hnc
  refine ⟨hnc,?_⟩
  let K := centralizer ({t} : Set (Equiv.Perm (Fin 6))) ⊓
    centralizer ({r} : Set (Equiv.Perm (Fin 6)))
  have hd18 : Nat.card K ∣ 18 :=
    (card_dvd_of_le (show K ≤ centralizer ({t} : Set _) from inf_le_left)).trans
      ((cubic_centralizer_card t ht).dvd)
  have hd16 : Nat.card K ∣ 16 :=
    (card_dvd_of_le (show K ≤ centralizer ({r} : Set _) from inf_le_right)).trans
      ((even_involution_centralizer_card r hr he).dvd)
  have hd2 : Nat.card K ∣ 2 := Nat.dvd_gcd hd18 hd16
  have hp : IsPGroup 2 (zpowers r) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hr,pow_one])
  have hm := card_modEq_card_inf_centralizer (zpowers r)
    (centralizer ({t} : Set (Equiv.Perm (Fin 6)))) hp (zpowers_le.mpr hnc)
  simp only [zpowers_eq_closure,centralizer_closure,cubic_centralizer_card t ht] at hm
  change 18 % 2 = Nat.card K % 2 at hm
  have hpK := Nat.card_pos (α := K)
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd2
  change Nat.card K = 2
  omega

end Theory.SpecificGroups.SymmetricSix
