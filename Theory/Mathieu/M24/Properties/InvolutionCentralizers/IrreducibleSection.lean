module
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.CoreCenter
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoCentral
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.GroupAction.FullyMovedIrreducibleOvergroup
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupTheory.EvenCentralizerFixedInvolution
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.Quasithin.EvenCharacteristic
/-!
# Odd centralizers of marked irreducible sections in M₂₄

An even centralizer of a Sylow-normalized actor contains an involution fixed
by that full Sylow. Native fusion identifies its centralizer with the actual
2A centralizer. The fully moved irreducible section must lie in the center
of its two-core, whose order is at most two. A larger section is impossible.
Innerness then makes every involutory pointwise fixer of the actor trivial.

Source: Aschbacher--Smith 10.2.9, printed pp.750--751; GLS3 Table 5.3e.
The original natural and dual binary-three point sections consume this result.
-/

public section
namespace Sporadic.Mathieu.M24InvolutionCentralizers
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.DoubleCoverCentralizer

theorem centralizer_odd_of_irreducible_section
    (S : Sylow 2 M24) (B E : Subgroup M24) (hB : IsPPerfect 2 B)
    (hSB : (S : Subgroup M24) ≤ normalizer (B : Set M24))
    (hSE : (S : Subgroup M24) ≤ normalizer (E : Set M24))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B) (hc : 2 < Nat.card E)
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set M24)) (hmove : ⁅E,B⁆ = E)
    (hirr : ∀ N : Subgroup M24, E ⊓ centralizer (B : Set M24) ≤ N → N ≤ E →
      B ≤ normalizer (N : Set M24) → N = E ⊓ centralizer (B : Set M24) ∨ N = E) :
    ¬ 2 ∣ Nat.card (centralizer (B : Set M24)) := by
  intro heven
  obtain ⟨z,hz,h⟩ := exists_involution_centralizing_normalizing_two_group
    B (S : Subgroup M24) S.isPGroup' hSB heven
  let K := centralizer ({z} : Set M24)
  have hBK : B ≤ K := le_sup_left.trans h
  have hSK : (S : Subgroup M24) ≤ K := le_sup_right.trans h
  obtain ⟨hzS,hzcomm⟩ := MulAut.involution_mem_sylow_of_centralizes S z
    ((orderOf_eq_prime_iff.mp hz).1) (by
      intro s hs
      apply mul_inv_eq_iff_eq_mul.mpr
      exact (mem_centralizer_singleton_iff.mp (hSK hs)).symm)
  have hzc : TwoCentral z := ⟨S,hzS,mem_center_iff.mpr (fun s =>
    Subtype.ext (hzcomm s s.property).eq.symm)⟩
  obtain ⟨g,hg⟩ := isConj_iff.mp (isConj_twoA_of_twoCentral z hz hzc).symm
  have hmap : K.map (MulAut.conj g).toMonoidHom = centralizer2A := by
    rw [map_centralizer_equiv,Set.image_singleton,MulAut.conj_apply,hg]
  let e : K ≃* centralizer2A := ((MulAut.conj g).subgroupMap K).trans
    (MulEquiv.subgroupCongr hmap)
  have hchar : centralizer (pCore 2 centralizer2A : Set centralizer2A) ≤
      pCore 2 centralizer2A := by
    rw [←TwoA.kernel_eq_twoCore]
    exact TwoA.kernel_selfCentralizing
  have hbound := Theory.GroupAction.fully_moved_irreducible_card_le_overgroup_core_center
    S B E K hB hSB hSE hE hEB hcore hmove hirr hBK hSK
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr hchar)
  let eP : pCore 2 K ≃* pCore 2 centralizer2A :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  have hh := TwoA.core_center_card_le_two
  rw [← Nat.card_congr (centerCongr eP).toEquiv] at hh
  exact (not_lt_of_ge (hbound.trans hh)) hc

theorem eq_one_of_fixes_odd_centralizer
    (B : Subgroup M24) (ho : ¬ 2 ∣ Nat.card (centralizer (B : Set M24)))
    (a : MulAut M24) (ha : a^2=1) (hf : ∀ x ∈ B, a x = x) : a=1 := by
  by_contra hne
  obtain ⟨x,he,hx⟩ := exists_inner_involution a (orderOf_eq_prime_iff.mpr ⟨ha,hne⟩)
  have hxc : x ∈ centralizer (B : Set M24) := by
    intro b hb
    have hh := hf b hb
    rw [he,MulAut.conj_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  apply ho
  simpa only [Subgroup.orderOf_mk,hx] using
    orderOf_dvd_natCard (⟨x,hxc⟩ : centralizer (B : Set M24))
end Sporadic.Mathieu.M24InvolutionCentralizers
