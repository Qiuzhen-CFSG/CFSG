module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.Divisibility
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import BenderSuzuki.MatrixGroups.SuzukiZero
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# Excluding M₂₂ and J₂ from the residual comparison

The source involution tables remain explicit inputs for automorphisms of the
actual sporadic carriers. An inner M₂₂ fixed subgroup has order 384, whereas
its two outer rows contain the odd prime 7 or 5. For J₂ the inner fixed
subgroups have orders 1920 and 240, whereas the outer row contains a copy of
L₃(2) through its faithful inner action and hence has order divisible by 7.

These numerical facts follow from actual extensions, central products and
model isomorphisms. Odd prime divisors survive both the passage to O² and
the covering maps with two-group kernels. The contrary containment therefore
forces an outer prime divisor into an inner fixed subgroup, a contradiction.
No identification of the two covering kernels is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(5),(8), printed pp.1171–1172, and the comparison in the proof of
16.4.11(2), printed p.1193. This module proves the two exclusions conditional
on those earlier tables; it does not assert the tables themselves.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
open Subgroup Theory.GroupTheory

private theorem extension_card {N E Q : Type*} [Group N] [Group E] [Group Q]
    (s : GroupExtension N E Q) : Nat.card E = Nat.card N * Nat.card Q := by
  have hn : Nat.card N = Nat.card s.rightHom.ker := by
    rw [← s.range_inl_eq_ker_rightHom]
    exact Nat.card_congr (MonoidHom.ofInjective s.inl_injective).toEquiv
  rw [← s.rightHom.ker.card_mul_index, ← hn, index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      s.rightHom s.rightHom_surjective).toEquiv]

private theorem elementary_card (n : ℕ) :
    Nat.card (OtherPreliminaries.Mathieu.Elementary n) = 2 ^ n := by
  simp [OtherPreliminaries.Mathieu.Elementary, OtherPreliminaries.Mathieu.C2]

private theorem m22_inner_card (a : MulAut Sporadic.Mathieu.M22)
    (h : OtherPreliminaries.Mathieu.M22InvolutionAlternative a)
    (hi : ∃ x, a = MulAut.conj x) : Nat.card a.fixedSubgroup = 384 := by
  rcases h with ⟨_, ⟨s⟩⟩ | ⟨ho, _⟩
  · rw [extension_card s, elementary_card]
    change 2 ^ 4 * Nat.card (Equiv.Perm (Fin 4)) = 384
    rw [Nat.card_perm]
    norm_num
  · exact (ho hi).elim

private theorem m22_outer_prime (a : MulAut Sporadic.Mathieu.M22)
    (h : OtherPreliminaries.Mathieu.M22InvolutionAlternative a)
    (ho : ¬ ∃ x, a = MulAut.conj x) :
    7 ∣ Nat.card a.fixedSubgroup ∨ 5 ∣ Nat.card a.fixedSubgroup := by
  rcases h with ⟨hi, _⟩ | ⟨_, h⟩
  · exact (ho hi).elim
  rcases h with hs | hs
  · left
    obtain ⟨s⟩ := hs
    have hc := extension_card s
    rw [elementary_card, Matrix.PSL3Two.card_PSL] at hc
    rw [hc]
    norm_num
  · right
    obtain ⟨s⟩ := hs
    have hc := extension_card s
    rw [elementary_card, BenderSuzuki.MatrixGroups.suzukiZero_card] at hc
    rw [hc]
    norm_num

private theorem quaternion_dihedral_card {Q : Type*} [Group Q] [Finite Q]
    (h : OtherPreliminaries.JankoTwoHigmanSims.IsQuaternionDihedralProduct Q) :
    Nat.card Q = 32 := by
  obtain ⟨B, D, ⟨eB⟩, ⟨eD⟩, hi, hcomm, hsup⟩ := h
  have hB : Nat.card B = 8 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hD : Nat.card D = 8 := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  have hn : D ≤ normalizer (B : Set Q) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro d hd b hb
    exact hcomm b hb d hd
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes B D hn
  rw [hB, hD, hi, hsup, card_top] at hc
  omega

private theorem j2_core_card {C : Type*} [Group C] [Finite C]
    (h : OtherPreliminaries.JankoTwoHigmanSims.IsJ2CoreExtension C) :
    Nat.card C = 1920 := by
  obtain ⟨Q, hn, hQ, ⟨e⟩⟩ := h
  let := hn
  rw [card_eq_card_quotient_mul_card_subgroup Q, Nat.card_congr e.toEquiv,
    quaternion_dihedral_card hQ]
  change Nat.card (alternatingGroup (Fin 5)) * 32 = 1920
  rw [nat_card_alternatingGroup]
  norm_num

private theorem j2_inner_not_seven (a : MulAut Sporadic.LeechRelated.J2.Carrier)
    (h : OtherPreliminaries.JankoTwoHigmanSims.J2InvolutionAlternative a)
    (hi : ∃ x, a = MulAut.conj x) : ¬ 7 ∣ Nat.card a.fixedSubgroup := by
  rcases h with ⟨_, h⟩ | ⟨ho, _⟩
  · rcases h with hc | he
    · rw [j2_core_card hc]
      norm_num
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, Nat.card_prod]
      change ¬ 7 ∣ Nat.card (Fin 2 → Multiplicative (ZMod 2)) *
        Nat.card (alternatingGroup (Fin 5))
      rw [nat_card_alternatingGroup]
      norm_num
  · exact (ho hi).elim

private theorem seven_dvd_aut_l3two :
    7 ∣ Nat.card (MulAut Matrix.PSL3Two.PSL) := by
  have hc : center Matrix.PSL3Two.PSL = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have h := (centerCongr Matrix.PSL3Two.equiv).symm ⟨x, hx⟩ |>.property
    change Matrix.PSL3Two.equiv.symm x ∈ center Matrix.PSL3Two.SL at h
    have he : Matrix.PSL3Two.equiv.symm x = 1 :=
      mem_bot.mp (Matrix.PSL3Two.center_eq_bot.le h)
    exact mem_bot.mpr (Matrix.PSL3Two.equiv.symm.map_eq_one_iff.mp he)
  have hd := card_dvd_of_injective (MulAut.conj : Matrix.PSL3Two.PSL →* _)
    (conj_injective_of_center_eq_bot hc)
  rw [Matrix.PSL3Two.card_PSL] at hd
  exact dvd_trans (by norm_num : 7 ∣ 168) hd

private theorem j2_outer_seven (a : MulAut Sporadic.LeechRelated.J2.Carrier)
    (h : OtherPreliminaries.JankoTwoHigmanSims.J2InvolutionAlternative a)
    (ho : ¬ ∃ x, a = MulAut.conj x) : 7 ∣ Nat.card a.fixedSubgroup := by
  rcases h with ⟨hi, _⟩ | ⟨_, ⟨e⟩⟩
  · exact (ho hi).elim
  · rw [Nat.card_congr e.toEquiv]
    exact seven_dvd_aut_l3two

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

private theorem not_quotient_model_of_separating_prime_rows (d : Contrary T z L g R r)
    {S : Type*} [Group S] [Finite S] (e : (L ⧸ center L) ≃* S)
    (hrows : ∀ a b : MulAut S, orderOf a = 2 → orderOf b = 2 →
      (∃ x, a = MulAut.conj x) → (¬ ∃ x, b = MulAut.conj x) →
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card b.fixedSubgroup ∧
        ¬ q ∣ Nat.card a.fixedSubgroup) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let ec : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
  let : IsQuasisimple (L.conjBy g) := IsQuasisimple.of_mulEquiv ec
  let eM := (centralQuotientCongr ec).symm.trans e
  let hi := d.setup.sylow_normalizes (d.setup.le_sylow d.mem)
  let a := MulAut.centralQuotientAction e (action hi)
  let b := MulAut.centralQuotientAction eM (action d.z_normalizes)
  have ha : orderOf a = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) _).trans d.inner_action_order
  have hb : orderOf b = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction eM)
      (MulAut.centralQuotientAction_injective eM) _).trans d.outer_action_order
  have hia : ∃ x : S, a = MulAut.conj x :=
    (MulAut.centralQuotientAction_inner_iff e (action hi)).mpr d.inner_action
  have hob : ¬ ∃ x : S, b = MulAut.conj x := fun h =>
    d.outer_action ((MulAut.centralQuotientAction_inner_iff eM _).mp h)
  obtain ⟨q, hq, hq2, hout, hin⟩ := hrows a b ha hb hia hob
  have hbo := (odd_prime_dvd_residual_iff hq hq2).mpr hout
  have ho : q ∣ Nat.card (centralImage (L.conjBy g) (residual (L.conjBy g) z)) := by
    rw [Nat.card_congr (centralImageModelEquiv (conjugate_oddCore d) eM
      d.z_normalizes).toEquiv]
    exact hbo
  have hai := outer_odd_prime_dvd_inner d hq hq2 ho
  rw [Nat.card_congr (centralImageModelEquiv (component_oddCore d) e hi).toEquiv] at hai
  exact hin ((odd_prime_dvd_residual_iff hq hq2).mp hai)

/-- The M₂₂ quotient is incompatible with the contrary residual containment,
using precisely the earlier source involution table. -/
theorem not_m22_quotient (d : Contrary T z L g R r)
    (rows : ∀ a : MulAut Sporadic.Mathieu.M22, orderOf a = 2 →
      OtherPreliminaries.Mathieu.M22InvolutionAlternative a)
    (e : (L ⧸ center L) ≃* Sporadic.Mathieu.M22) : False := by
  apply not_quotient_model_of_separating_prime_rows d e
  intro a b ha hb hi ho
  have hcard := m22_inner_card a (rows a ha) hi
  rcases m22_outer_prime b (rows b hb) ho with h7 | h5
  · exact ⟨7, by norm_num, by norm_num, h7, by rw [hcard]; norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, h5, by rw [hcard]; norm_num⟩

/-- The J₂ quotient is incompatible with the contrary residual containment,
using precisely the earlier source involution table. -/
theorem not_j2_quotient (d : Contrary T z L g R r)
    (rows : ∀ a : MulAut Sporadic.LeechRelated.J2.Carrier, orderOf a = 2 →
      OtherPreliminaries.JankoTwoHigmanSims.J2InvolutionAlternative a)
    (e : (L ⧸ center L) ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  exact not_quotient_model_of_odd_prime_fixed_rows d e (by norm_num : Nat.Prime 7)
    (by norm_num) (fun a ha hi => j2_inner_not_seven a (rows a ha) hi)
    (fun a ha ho => j2_outer_seven a (rows a ha) ho)

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
