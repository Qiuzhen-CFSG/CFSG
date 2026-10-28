module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.GroupAction.FullyMovedIrreducibleOvergroup
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# J₄ centralizers of fully moved irreducible sections

An even centralizer of a Sylow-normalized actor supplies a central involution
of that Sylow. The second involution centralizer has insufficient two-part.
In the first, a fully moved irreducible section must lie in the center of the
extraspecial two-core, which has order two. Thus a larger section forces an
odd centralizer. Since J₄ automorphisms are inner, its involutory pointwise
fixers are trivial.

Source application: Aschbacher--Smith A.3.12 and 10.2.9, pp.47--48,750--751.
The original natural binary-three point section is the consumer.
-/

public section
namespace Janko4
open Subgroup Theory.GroupTheory
open InvolutionCentralizers
attribute [local irreducible] modelGroup matrixA matrixB

theorem centralizer_odd_of_irreducible_section
    (S : Sylow 2 Model) (B E : Subgroup Model) (hB : IsPPerfect 2 B)
    (hSB : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (hSE : (S : Subgroup Model) ≤ normalizer (E : Set Model))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B) (hc : 2 < Nat.card E)
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set Model)) (hmove : ⁅E,B⁆ = E)
    (hirr : ∀ N : Subgroup Model, E ⊓ centralizer (B : Set Model) ≤ N → N ≤ E →
      B ≤ normalizer (N : Set Model) → N = E ⊓ centralizer (B : Set Model) ∨ N = E) :
    ¬ 2 ∣ Nat.card (centralizer (B : Set Model)) := by
  intro heven
  obtain ⟨z,hz,h⟩ := exists_involution_centralizing_normalizing_two_group
    B (S : Subgroup Model) S.isPGroup' hSB heven
  let K := centralizer ({z} : Set Model)
  have hBK : B ≤ K := le_sup_left.trans h
  have hSK : (S : Subgroup Model) ≤ K := le_sup_right.trans h
  rcases centralizer_equiv_first_or_second z hz with hfirst | hsecond
  · obtain ⟨e⟩ := hfirst
    have hbound := Theory.GroupAction.fully_moved_irreducible_card_le_overgroup_core_center
      S B E K hB hSB hSE hE hEB hcore hmove hirr hBK hSK
      (centralizer_characteristic_two z hz)
    let eP : pCore 2 K ≃* pCore 2 First.centralizer :=
      (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
    have hcc := Nat.card_congr (centerCongr eP).toEquiv
    let := First.centralizer_twoCore_extraspecial
    rw [IsExtraspecial.center_order_p 2 (pCore 2 First.centralizer)] at hcc
    omega
  · obtain ⟨e⟩ := hsecond
    have hdiv : 2^21 ∣ Nat.card S := by
      have hd : 2^21 ∣ Nat.card Model := by rw [Cardinality.model_card]; norm_num
      rw [←(S : Subgroup Model).card_mul_index] at hd
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr S.not_dvd_index).pow_left 21
        |>.dvd_of_dvd_mul_right hd
    have hd := hdiv.trans (card_dvd_of_le hSK)
    rw [Nat.card_congr e.toEquiv,Second.ambient_card] at hd
    norm_num at hd

end Janko4

namespace Janko4
open Subgroup
/-- An inner involutory pointwise fixer vanishes when the actual centralizer is odd. -/
theorem eq_one_of_fixes_odd_centralizer (hz : center Model = ⊥)
    (B : Subgroup Model) (ho : ¬ 2 ∣ Nat.card (centralizer (B : Set Model)))
    (a : MulAut Model) (ha : a^2=1) (hf : ∀ x ∈ B, a x = x) : a=1 := by
  by_contra hne
  obtain ⟨g,hg⟩ := Janko4.AdequateLocal.exists_eq_conj a
  obtain ⟨x,hx,he,_⟩ := MulAut.inner_involution_representative hz a
    (orderOf_eq_prime_iff.mpr ⟨ha,hne⟩) ⟨g,hg⟩
  have hxc : x ∈ centralizer (B : Set Model) := by
    intro b hb
    have hh := hf b hb
    rw [he,MulAut.conj_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  apply ho
  simpa only [Subgroup.orderOf_mk,hx] using
    orderOf_dvd_natCard (⟨x,hxc⟩ : centralizer (B : Set Model))
end Janko4
