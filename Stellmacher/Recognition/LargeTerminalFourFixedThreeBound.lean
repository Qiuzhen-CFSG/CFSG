module

public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData
public import Stellmacher.Recognition.LargeTerminalFourFixedCoreFrattini
public import Theory.GroupTheory.CharacteristicTwoFrattiniThreeBound

/-!
# Reduction of the fixed-involution three-bound to its core structure

The terminal context makes every involution centralizer of characteristic
two. A bound of 32 on the Frattini quotient of its two-core therefore excludes
27, and hence 81, from the centralizer order by the faithful Frattini action.

Nonfusion also bounds the full fixed-involution centralizer's Sylow
two-subgroups by 2048: a Sylow of order 4096 would make the involution
conjugate to the unique omega-central involution. The prescribed Sylow
intersection has the sharper bound 256 from the local centralizer estimates.

The structural bound on the actual five-fixed involution's core is a separate
input here. This module does not yet establish the unconditional terminal
three-bound required for the last four-group contradiction in Thompson VI,
printed p.630.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven Subgroup

universe u

/-- The remaining structural input can be stated solely in terms of the
actual involution centralizer's two-core Frattini quotient. -/
public theorem LargeTerminalContext.not_eightyone_dvd_involution_centralizer_of_frattini_bound
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (y : G) (hy : orderOf y = 2)
    (hbound : Nat.card (pCore 2 (centralizer ({y} : Set G)) ⧸
      frattini (pCore 2 (centralizer ({y} : Set G)))) ≤ 32) :
    ¬ 81 ∣ Nat.card (centralizer ({y} : Set G)) := by
  have hchar := (ctx.localStructure _
    (Theory.GroupTheory.isTwoLocal_involution_centralizer hy)).2
  intro h
  exact not_twentyseven_dvd_card_of_characteristic_two_frattini_le_thirtytwo
    hchar hbound ((by decide : 27 ∣ 81).trans h)

private theorem sylow_not_le_centralizer
    {G : Type*} [Group G] [Finite G] (S P : Sylow 2 G)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (y : G) (hy : orderOf y = 2) (hnonfusion : ¬ IsConj z y) :
    ¬ (P : Subgroup G) ≤ centralizer ({y} : Set G) := by
  classical
  intro hPC
  let C := centralizer ({y} : Set G)
  have hyK : y ∈ twoCoreIn C := central_involution_mem_twoCore C y
    (mem_centralizer_singleton_iff.mpr rfl) le_rfl
    (by rw [← hy]; exact pow_orderOf_eq_one y)
  have hyP : y ∈ (P : Subgroup G) := by
    obtain ⟨a, ha, hval⟩ := hyK
    change (a : G) = y at hval
    have hp := (pCore_isPGroup (p := 2) (G := C)).le_sylow_of_normal (P.subtype hPC) ha
    change (a : G) ∈ (P : Subgroup G) at hp
    simpa only [hval] using hp
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  let e := MulAut.conj g
  have hmap : (P : Subgroup G).map e.toMonoidHom = (S : Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  have hey : e y ∈ omegaOneCenter (S : Subgroup G) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hmap ▸ mem_map_of_mem e.toMonoidHom hyP, ?_, ?_⟩
    · rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
    · intro s hs
      rw [← hmap] at hs
      obtain ⟨p, hp, rfl⟩ := hs
      change e p * e y = e y * e p
      simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp (hPC hp))
  rw [← hgen, mem_zpowers_iff_mem_range_orderOf, hz] at hey
  have heyz : e y = z := by
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hey
    have hk2 := Finset.mem_range.mp hk
    interval_cases k
    · have hye : y = 1 := e.injective (by simpa using heq.symm)
      simp [hye] at hy
    · simpa using heq.symm
  apply hnonfusion
  exact (isConj_iff.mpr ⟨g, heyz⟩).symm

/-- Nonfusion excludes a Sylow-central fixed involution. Thus the full
centralizer has Sylow two-subgroups of order at most half the ambient Sylow
order. This controls the full centralizer, but does not give the needed
Frattini quotient bound. -/
public theorem LargeTerminalContext.fixed_involution_centralizer_sylow_card_le
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (y : G) (hy : orderOf y = 2)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual)
    (T : Sylow 2 (centralizer ({y} : Set G))) : Nat.card T ≤ 2048 := by
  let C := centralizer ({y} : Set G)
  let U := (T : Subgroup C).map C.subtype
  obtain ⟨P, hUP⟩ := (T.isPGroup'.map C.subtype).exists_le_sylow
  have hPcard : Nat.card P = 4096 := (Nat.card_congr (P.equiv S).toEquiv).trans hS
  have hUcard : Nat.card U = Nat.card T := card_map_of_injective C.subtype_injective
  have hdiv : Nat.card T ∣ 2 ^ 12 := by
    have hh := card_dvd_of_le hUP
    rwa [hUcard, hPcard] at hh
  have hne : Nat.card T ≠ 4096 := by
    intro hh
    have heq : U = (P : Subgroup G) := eq_of_le_of_card_ge hUP
      (by rw [hUcard, hh, hPcard])
    apply sylow_not_le_centralizer S P z hz hgen y hy
      (ctx.not_isConj_of_five_normalizer_le_second hS A hA hN z hz hgen y hyA hyR)
    rw [← heq]
    exact map_subtype_le _
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hklt : k ≤ 11 := by
    by_contra! h
    have heq : k = 12 := by omega
    exact hne (by simpa [heq] using hcard)
  rw [hcard]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hklt)

end Stellmacher.Recognition
