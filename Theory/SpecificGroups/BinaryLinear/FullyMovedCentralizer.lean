module
public import Theory.SpecificGroups.BinaryLinear.IrreducibleSectionCentralizer
public import Theory.GroupAction.PerfectMovedSmallCenter

/-!
# Odd centralizers of fully moved sections in binary linear groups

An even centralizer supplies an involution centralized by the full Sylow.
The native involution-centralizer geometry gives a self-centralizing two-core
whose center has order at most two. The commuting fixed-point argument
excludes the original nonzero fully moved elementary section, without any
irreducibility assumption or choice of coordinates.

Source: Aschbacher--Smith A.3.12 and 10.2.9, pp.47--48,750--751.
The non-A₅ point-component comparison is the actual consumer.
-/

public section
open Subgroup Theory.GroupTheory
namespace BinaryLinear

/-- Full-Sylow normalization and a nonzero fully moved section force odd centralizer. -/
theorem centralizer_odd_of_fully_moved_section {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (hV : 2 ∣ Nat.card V)
    (hd : 1 < Module.finrank (ZMod 2) V)
    (S : Sylow 2 (BinaryLinear.GL V)) (B E : Subgroup (BinaryLinear.GL V)) [Group.IsPerfect B] (hB : IsPPerfect 2 B)
    (hSB : (S : Subgroup (BinaryLinear.GL V)) ≤ normalizer (B : Set (BinaryLinear.GL V)))
    (hSE : (S : Subgroup (BinaryLinear.GL V)) ≤ normalizer (E : Set (BinaryLinear.GL V)))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B) (hc : 2 < Nat.card E)
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set (BinaryLinear.GL V))) (hmove : ⁅E,B⁆ = E)
    :
    ¬ 2 ∣ Nat.card (centralizer (B : Set (BinaryLinear.GL V))) := by
  let : Finite (BinaryLinear.GL V) := Finite.of_injective (fun a : BinaryLinear.GL V => (a : V → V)) DFunLike.coe_injective
  intro heven
  obtain ⟨z,hz,h⟩ := exists_involution_centralizing_normalizing_two_group
    B (S : Subgroup (BinaryLinear.GL V)) S.isPGroup' hSB heven
  have hz1 := (orderOf_eq_prime_iff.mp hz).2
  obtain ⟨w,f,hw,hf,hfw,hform⟩ := central_sylow_eq_transvection hV hd S hz1
    (fun s hs => mem_centralizer_singleton_iff.mp ((le_sup_right.trans h : (S : Subgroup (BinaryLinear.GL V)) ≤ _) hs))
  have he : z = transvection w f hfw := LinearEquiv.ext hform
  subst z
  let K := (MulAut.conj (transvection w f hfw)).fixedSubgroup
  have hK : K = centralizer ({transvection w f hfw} : Set (BinaryLinear.GL V)) := MulAut.fixedSubgroup_conj _
  have hBK : B ≤ K := hK.symm ▸ le_sup_left.trans h
  have hSK : (S : Subgroup (BinaryLinear.GL V)) ≤ K := hK.symm ▸ le_sup_right.trans h
  have hbound := Theory.GroupAction.fully_moved_eq_bot_of_overgroup_small_core_center
    S B E K hB hSB hSE hE hEB hcore hmove hBK hSK
    (inner_involution_twoCore (transvection w f hfw) (orderOf_eq_prime_iff.mp hz).1 hz1)
  have hh : Nat.card (center (pCore 2 K)) ≤ 2 := by
    exact transvection_core_center_card_le_two hw hf hfw
  have he := hbound (hh.trans (by decide))
  rw [he,card_bot] at hc
  omega

end BinaryLinear
