module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.ConcreteAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.LocalReduction
public import Theory.GroupTheory.PPerfectHom


/-!
# The whole two-perfect Suzuki actor

The Borel quotient detector excludes order three in the automorphism image.
The source actor has order supported on two and three, so that image is a
two-group. Two-perfectness then kills the whole action. This uses neither
an exponent-three assumption nor a lift of order-three automorphisms to
order-three elements of the actor.

The ambient conjugation application combines this argument with the actual
intersection calculation on the Borel two-core quotient.

Source: Aschbacher–Smith, 13.8.16, printed pp.952–953, with the Borel
automorphism calculation of F.1.3(1), combined manuscript (1 March 2004).
-/

public section

open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource

variable {A K : Type*} [Group A] [Finite A] [Group K]

theorem card_two_three (hA : IsPGroup 3 (A ⧸ pCore 2 A)) :
    ∃ r s : ℕ, Nat.card A = 2 ^ r * 3 ^ s := by
  obtain ⟨r, hr⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  obtain ⟨s, hs⟩ := hA.exists_card_eq
  exact ⟨r, s, by simpa only [index_eq_card, hr, hs] using (pCore 2 A).card_mul_index.symm⟩

theorem action_eq_one (B : Subgroup K) (hd : DetectsThreeAutomorphisms B)
    (hp : IsPPerfect 2 A) (hc : ∃ r s : ℕ, Nat.card A = 2 ^ r * 3 ^ s)
    (f : A →* MulAut K)
    (hb : ∀ a : A, ∀ b ∈ B, f a b * b⁻¹ ∈ B.pCoreIn 2) : f = 1 := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hthree : ¬ 3 ∣ Nat.card f.range := by
    intro h
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 h
    have ha3 : (a : MulAut K) ^ 3 = 1 := by
      have he : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
      exact congrArg Subtype.val he
    obtain ⟨x, hx⟩ := a.property
    have he : (a : MulAut K) = 1 := hd a ha3 (by simpa only [← hx] using hb x)
    have : a = 1 := Subtype.ext he
    simp [this] at ha
  have hrange : IsPGroup 2 f.range := by
    obtain ⟨r, s, hcard⟩ := hc
    have hdvd := card_range_dvd f
    rw [hcard] at hdvd
    have hcop : (Nat.card f.range).Coprime (3 ^ s) :=
      ((Nat.prime_three.coprime_iff_not_dvd.mpr hthree).symm).pow_right s
    exact IsPGroup.of_card_dvd_pow (hcop.dvd_of_dvd_mul_right hdvd)
  have he := hp.hom_eq_one_of_isPGroup hrange f.rangeRestrict
  apply MonoidHom.ext
  intro a
  exact congrArg Subtype.val (DFunLike.congr_fun he a)

variable {G : Type*} [Group G] [Finite G]

theorem centralizes_of_detector {L B D : Subgroup G}
    (hBD : B ≤ D) (hD : DetectsThreeAutomorphisms (B.subgroupOf D))
    (hp : IsPPerfect 2 L) (hc : ∃ r s : ℕ, Nat.card L = 2 ^ r * 3 ^ s)
    (hn : L ≤ normalizer (D : Set G))
    (hb : ⁅L, B⁆ ≤ B.pCoreIn 2) : L ≤ centralizer (D : Set G) := by
  let f : L →* MulAut D := D.normalizerMonoidHom.comp (inclusion hn)
  have he : f = 1 := action_eq_one (B.subgroupOf D) hD hp hc f (by
    intro a b hb'
    have hmap : ((B.subgroupOf D).pCoreIn 2).map D.subtype = B.pCoreIn 2 := by
      rw [map_pCoreIn_of_injective 2 _ D.subtype D.subtype_injective,
        map_subgroupOf_eq_of_le hBD]
    have hh : ((f a b * b⁻¹ : D) : G) ∈ B.pCoreIn 2 := by
      exact hb (commutator_mem_commutator a.property hb')
    rw [← hmap] at hh
    obtain ⟨x, hx, he⟩ := hh
    exact (Subtype.ext he : x = f a b * b⁻¹) ▸ hx)
  intro a ha
  rw [mem_centralizer_iff]
  intro d hd
  have he' := congrArg (fun α : MulAut D => (α ⟨d, hd⟩ : G))
    (DFunLike.congr_fun he ⟨a, ha⟩)
  change a * d * a⁻¹ = d at he'
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

theorem centralizes_of_mutual_normalization {L B D : Subgroup G}
    (hBD : B ≤ D) (hD : DetectsThreeAutomorphisms (B.subgroupOf D))
    (hp : IsPPerfect 2 L) (hq : IsPGroup 3 (L ⧸ pCore 2 L))
    (hn : L ≤ normalizer (D : Set G)) (hthree : ¬ 3 ∣ Nat.card B)
    (hLB : L ≤ normalizer (B : Set G)) (hBL : B ≤ normalizer (L : Set G)) :
    L ≤ centralizer (D : Set G) :=
  centralizes_of_detector hBD hD hp (card_two_three hq) hn
    (commutator_le_borel_twoCore hq hthree hLB hBL)

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource
