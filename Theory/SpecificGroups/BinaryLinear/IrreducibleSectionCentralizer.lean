module
public import Theory.SpecificGroups.BinaryLinear.TransvectionCoreCenter
public import Theory.SpecificGroups.BinaryLinear.InnerInvolutionComponents
public import Theory.SpecificGroups.BinaryLinear.FiveSevenFixer
public import Theory.GroupAction.FullyMovedIrreducibleOvergroup
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupTheory.EvenCentralizerFixedInvolution
/-!
# Centralizers of fully moved irreducible sections in binary linear groups

A full Sylow normalizing an actor with even centralizer fixes an involution
in that centralizer. Such a Sylow-central element is a transvection. Its
centralizer has characteristic two and a two-core center of order at most
two, which cannot contain a larger fully moved irreducible section.
In degree five a seven-element also excludes graph automorphisms, so an
involutory pointwise fixer of the actor is trivial.

Source: Aschbacher--Smith 10.2.9, printed pp.750--751. The actual L₅(2)
point-component comparison consumes the natural and dual specializations.
-/

public section
open Subgroup Theory.GroupTheory
namespace BinaryLinear

/-- Full-Sylow normalization and the chosen irreducible section force odd centralizer. -/
theorem centralizer_odd_of_irreducible_section {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (hV : 2 ∣ Nat.card V)
    (hd : 1 < Module.finrank (ZMod 2) V)
    (S : Sylow 2 (BinaryLinear.GL V)) (B E : Subgroup (BinaryLinear.GL V)) (hB : IsPPerfect 2 B)
    (hSB : (S : Subgroup (BinaryLinear.GL V)) ≤ normalizer (B : Set (BinaryLinear.GL V)))
    (hSE : (S : Subgroup (BinaryLinear.GL V)) ≤ normalizer (E : Set (BinaryLinear.GL V)))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B) (hc : 2 < Nat.card E)
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set (BinaryLinear.GL V))) (hmove : ⁅E,B⁆ = E)
    (hirr : ∀ N : Subgroup (BinaryLinear.GL V), E ⊓ centralizer (B : Set (BinaryLinear.GL V)) ≤ N → N ≤ E →
      B ≤ normalizer (N : Set (BinaryLinear.GL V)) → N = E ⊓ centralizer (B : Set (BinaryLinear.GL V)) ∨ N = E) :
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
  have hbound := Theory.GroupAction.fully_moved_irreducible_card_le_overgroup_core_center
    S B E K hB hSB hSE hE hEB hcore hmove hirr hBK hSK
    (inner_involution_twoCore (transvection w f hfw) (orderOf_eq_prime_iff.mp hz).1 hz1)
  have hh : Nat.card (center (pCore 2 K)) ≤ 2 := by
    exact transvection_core_center_card_le_two hw hf hfw
  exact (not_lt_of_ge (hbound.trans hh)) hc

open OuterCyclic

theorem five_eq_one_of_fixes_odd_centralizer (hz : center (LinearGroup 5) = ⊥)
    (B : Subgroup (LinearGroup 5)) (ho : ¬ 2 ∣ Nat.card (centralizer (B : Set (LinearGroup 5))))
    (h7 : 7 ∣ Nat.card B)
    (a : MulAut (LinearGroup 5)) (ha : a^2=1) (hf : ∀ x ∈ B, a x = x) : a=1 := by
  let : Finite (LinearGroup 5) := Finite.of_injective
    (fun a : LinearGroup 5 => (a : Space 5 → Space 5)) DFunLike.coe_injective
  by_contra hne
  obtain ⟨g,hg | hg⟩ := inner_graph (.inr rfl) a
  · obtain ⟨x,hx,he,_⟩ := MulAut.inner_involution_representative hz a
      (orderOf_eq_prime_iff.mpr ⟨ha,hne⟩) ⟨g,hg⟩
    have hxc : x ∈ centralizer (B : Set (LinearGroup 5)) := by
      intro b hb
      have hh := hf b hb
      rw [he,MulAut.conj_apply] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    apply ho
    simpa only [Subgroup.orderOf_mk,hx] using
      orderOf_dvd_natCard (⟨x,hxc⟩ : centralizer (B : Set (LinearGroup 5)))
  · let : Fact (Nat.Prime 7) := ⟨by decide⟩
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 7 h7
    have hx7 : (x : LinearGroup 5)^7=1 := congrArg Subtype.val (hx ▸ pow_orderOf_eq_one x)
    have hx1 := FiveSevenGraph.graph_fixed_seven_eq_one g (x : LinearGroup 5) hx7 (hg ▸ hf x x.property)
    have hne : (x : LinearGroup 5) ≠ 1 := by
      intro h
      have he : x = 1 := Subtype.ext h
      rw [he,orderOf_one] at hx
      omega
    exact hne hx1
end BinaryLinear
