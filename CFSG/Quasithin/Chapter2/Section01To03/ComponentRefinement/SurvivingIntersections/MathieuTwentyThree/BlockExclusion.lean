module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyThree.BlockOrders
public import Theory.GroupTheory.AlternatingPowerTwoExtension
public import Theory.GroupTheory.PPerfectHom
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Excluding chi-zero blocks from two-group extensions of A7 powers

Let N be normal in K with two-group quotient, and suppose N maps onto a
finite power of A7 with two-group kernel. Every block B of K lies in N by
two-perfection. Its images in the A7 coordinates are subnormal, hence trivial
or surjective. The kernel of the resulting product map is exactly O₂(B).
The embedded quotient B/O₂(B) has trivial center, so the short-group quotient
condition makes it simple. A nontrivial coordinate therefore identifies it
with A7. Its order 2520 excludes each of the actual chi-zero quotient models.

This proves the block exclusion for the stated extension structure; the local
overgroup realizing that structure is constructed separately by the M23
intersection argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, C.1.7 and C.1.12 (printed pp.123–124), and the
M23 case of 2.3.9(7)(f) (printed pp.525–526).
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement

open Subgroup ChapterC Theory.GroupTheory

private theorem a7_card : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup]
  norm_num

private theorem a7_not_twoGroup : ¬ IsPGroup 2 (alternatingGroup (Fin 7)) := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_card_dvd_pow
  rw [a7_card] at hn
  have hd : 3 ∣ 2 ^ n := (by decide : 3 ∣ 2520).trans hn
  have := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at this

/-- The coordinate dichotomy identifies the quotient of a short group with A7.
The two-group kernel and the trivial center of A7 are both essential. -/
private theorem short_quotient_card_of_a7_coordinates {B : Type*} [Group B]
    (hB : IsShort B) {n : ℕ} (g : B →* (Fin n → alternatingGroup (Fin 7)))
    (hker : IsPGroup 2 g.ker)
    (hcoord : ∀ i, (Pi.evalMonoidHom _ i).comp g = 1 ∨
      Function.Surjective ((Pi.evalMonoidHom _ i).comp g)) :
    Nat.card (B ⧸ pCore 2 B) = 2520 := by
  let : Finite B := hB.finite
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  -- A normal two-subgroup has trivial image in every nontrivial coordinate.
  have hcore : pCore 2 B = g.ker := by
    apply le_antisymm
    · intro b hb
      apply MonoidHom.mem_ker.mpr
      funext i
      rcases hcoord i with hi | hi
      · exact DFunLike.congr_fun hi b
      · let c := (Pi.evalMonoidHom _ i).comp g
        have : ((pCore 2 B).map c).Normal := Normal.map inferInstance c hi
        rcases (inferInstance : ((pCore 2 B).map c).Normal).eq_bot_or_eq_top with hh | hh
        · exact mem_bot.mp (hh ▸ mem_map_of_mem c hb)
        · have hp : IsPGroup 2 ((pCore 2 B).map c) := pCore_isPGroup.map c
          rw [hh] at hp
          exact (a7_not_twoGroup (hp.of_equiv topEquiv)).elim
    · exact le_sSup ⟨inferInstance, hker⟩
  let qg := QuotientGroup.lift (pCore 2 B) g hcore.le
  have hqg : Function.Injective qg :=
    (QuotientGroup.injective_lift_iff _ _ _).mpr hcore
  -- Central elements vanish in every coordinate of the faithful quotient map.
  have hcenter : center (B ⧸ pCore 2 B) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    apply mem_bot.mpr
    apply hqg
    rw [map_one]
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
    change g b = 1
    funext i
    rcases hcoord i with hi | hi
    · exact DFunLike.congr_fun hi b
    · have hc : g b i ∈ center (alternatingGroup (Fin 7)) := by
        rw [mem_center_iff]
        intro a
        obtain ⟨x, rfl⟩ := hi a
        have hh := congrArg (fun z => qg z i)
          (mem_center_iff.mp hz (QuotientGroup.mk' (pCore 2 B) x))
        simpa [qg] using hh
      simpa only [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 7)),
        mem_bot, Pi.one_apply] using hc
  -- The genuine short-group alternatives are quasisimplicity or order three.
  have : IsSimpleGroup (B ⧸ pCore 2 B) := by
    rcases hB.quotient with hq | hq
    · let := hq
      let := IsQuasisimple.simple (G := B ⧸ pCore 2 B)
      exact ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
        (QuotientGroup.quotientBot)).symm.isSimpleGroup
    · exact isSimpleGroup_of_prime_card hq
  obtain ⟨z, hz⟩ := exists_ne (1 : B ⧸ pCore 2 B)
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
  have hgb : g b ≠ 1 := fun hh => hz (hqg (hh.trans (map_one qg).symm))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hgb
  have hsurj : Function.Surjective ((Pi.evalMonoidHom _ i).comp g) := by
    rcases hcoord i with ht | ht
    · exact (hi (DFunLike.congr_fun ht b)).elim
    · exact ht
  let c := (Pi.evalMonoidHom _ i).comp qg
  have hc : Function.Surjective c := by
    intro a
    obtain ⟨b, hb⟩ := hsurj a
    exact ⟨QuotientGroup.mk' (pCore 2 B) b, hb⟩
  have hci : Function.Injective c := by
    apply (MonoidHom.ker_eq_bot_iff c).mp
    rcases (inferInstance : c.ker.Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · have ht : c = 1 := MonoidHom.ker_eq_top_iff.mp hh
      obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 7))
      obtain ⟨z, rfl⟩ := hc a
      exact (ha (DFunLike.congr_fun ht z)).elim
  exact (Nat.card_congr (MulEquiv.ofBijective c ⟨hci, hc⟩).toEquiv).trans a7_card

/-- No chi-zero block occurs in a finite two-group extension of an A7 power
with two-group kernel, with subnormality relative to the given ambient K. -/
theorem not_chiZeroBlockIn_of_alternatingPowerTwoExtension {K : Type*} [Group K] [Finite K]
    (hK : AlternatingPowerTwoExtension K 7) (B : Subgroup K) :
    ¬ IsChiZeroBlockIn B := by
  intro hB
  obtain ⟨N, hN, hquot, n, f, hf, hker⟩ := hK
  let := hN
  have hBN : B ≤ N := by
    have hh := hB.1.short.twoPerfect.hom_eq_one_of_isPGroup hquot
      ((QuotientGroup.mk' N).comp B.subtype)
    intro b hb
    exact (QuotientGroup.eq_one_iff b).mp (DFunLike.congr_fun hh ⟨b, hb⟩)
  let g := f.comp (inclusion hBN)
  have hgker : IsPGroup 2 g.ker :=
    hker.comap_of_injective (inclusion hBN) (inclusion_injective hBN)
  have hcoord : ∀ i, (Pi.evalMonoidHom _ i).comp g = 1 ∨
      Function.Surjective ((Pi.evalMonoidHom _ i).comp g) := by
    intro i
    let c := (Pi.evalMonoidHom _ i).comp f
    have hc : Function.Surjective c := by
      intro a
      obtain ⟨x, hx⟩ := hf (fun _ => a)
      exact ⟨x, congrFun hx i⟩
    have hs : ((Pi.evalMonoidHom _ i).comp g).range.IsSubnormal := by
      have he : ((Pi.evalMonoidHom _ i).comp g).range = (B.subgroupOf N).map c := by
        rw [show (Pi.evalMonoidHom _ i).comp g = c.comp (inclusion hBN) from rfl,
          MonoidHom.range_comp, inclusion_range]
      rw [he]
      exact hB.1.subnormal.subgroupOf.map hc
    rcases hs.eq_bot_or_top_of_isSimpleGroup
      (alternatingGroup.isSimpleGroup (by simp)) with hh | hh
    · exact Or.inl (MonoidHom.range_eq_bot_iff.mp hh)
    · exact Or.inr (MonoidHom.range_eq_top.mp hh)
  exact not_chiZero_of_quotient_card_2520
    (short_quotient_card_of_a7_coordinates hB.1.short g hgker hcoord) hB.2

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
