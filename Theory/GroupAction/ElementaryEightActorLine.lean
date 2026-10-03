module
public import Theory.GroupAction.ElementaryEightInvolution
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Propagating an elementary-eight commutator line

Let an elementary abelian two-subgroup A normalize an elementary abelian
subgroup V of order eight. If the commutator of a subgroup P≤V with A has
order two, then it equals the full commutator [V,A]. No A-invariance of P
is required.

Each nontrivial involution on V has a commutator of order two, by the fixed
subgroup cardinality and involution rank-nullity formula. An actor moving P
therefore has the prescribed line as its full commutator. Fix one such actor
a. For an actor b fixing P, the product ab moves P as a does. Since both a
and ab have commutators in the line, the commutator identity and normalization
of [P,A] by A give the same bound for b. Taking the generated commutator proves
equality.

This elementary action argument supplies the terminal-module core reduction
in Stellmacher (9.7), Journal of Algebra 190 (1997), printed p.54. The cyclic
involution helper was previously private in its campaign application.
-/
namespace Subgroup
open scoped commutatorElement IsMulCommutative
universe u

public theorem involution_commutator_card_two_on_elementary_eight
    {G : Type u} [Group G] [Finite G]
    (moduleGroup : Subgroup G) [IsElementaryAbelian 2 moduleGroup]
    (actor : G) (hactor : actor ≠ 1 ∧ actor ^ 2 = 1)
    (hnormal : Subgroup.zpowers actor ≤ Subgroup.normalizer (moduleGroup : Set G))
    (hcard : Nat.card moduleGroup = 8)
    (hne : ⁅moduleGroup, Subgroup.zpowers actor⁆ ≠ ⊥) :
    Nat.card (⁅moduleGroup, Subgroup.zpowers actor⁆ : Subgroup G) = 2 := by
  let actors := Subgroup.zpowers actor
  let _ : Subgroup.Normalizes actors moduleGroup := ⟨hnormal⟩
  let generator : actors := ⟨actor, Subgroup.mem_zpowers actor⟩
  have hgenerator : generator ≠ 1 ∧ generator ^ 2 = 1 := by
    constructor
    · intro heq
      exact hactor.1 (congrArg Subtype.val heq)
    · exact Subtype.ext hactor.2
  have hactors : Nat.card actors = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hactor.2 hactor.1]
  have hmap := commutatorAction_subgroup_conj_map_eq_commutator moduleGroup actors hnormal
  have hmoving : ∃ vector : moduleGroup, generator • vector ≠ vector := by
    by_contra! hfixed
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    apply Subgroup.zpowers_le.mpr
    rw [Subgroup.mem_centralizer_iff]
    intro vector hvector
    have heq := congrArg Subtype.val (hfixed ⟨vector, hvector⟩)
    change actor * vector * actor⁻¹ = vector at heq
    have heq' := congrArg (fun element : G => element * actor) heq
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq'.symm
  have hfixed := fixed_subgroup_card_four_of_nontrivial_involution_on_eight
    generator hgenerator hactors hcard hmoving
  let _ : Nontrivial moduleGroup := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hproduct := (card_two_action_fixed_commutator_card_data
    (U := moduleGroup) generator hgenerator hactors).1
  rw [hcard, hfixed] at hproduct
  rw [← hmap, Subgroup.card_map_of_injective moduleGroup.subtype_injective]
  omega


public theorem elementaryEight_commutator_line_of_subgroup
    {G : Type u} [Group G] [Finite G]
    (V A P : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hV : Nat.card V = 8) (hAV : A ≤ normalizer (V : Set G)) (hPV : P ≤ V)
    (hline : Nat.card (⁅P,A⁆ : Subgroup G) = 2) : ⁅V,A⁆ = ⁅P,A⁆ := by
  let L := ⁅P,A⁆
  have hlineL : Nat.card L = 2 := hline
  have hne : L ≠ ⊥ := by intro h; simp [h] at hlineL
  have hnA : A ≤ normalizer (L : Set G) := normalizer_commutator_ge_right P A
  have hsmall (a : G) (ha : a ∈ A) (hmove : ∃ p ∈ P, ⁅a,p⁆ ≠ 1) :
      ⁅V, zpowers a⁆ ≤ L := by
    have hane : a ≠ 1 := by rintro rfl; simp at hmove
    have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian a ha
    obtain ⟨p,hp,hpne⟩ := hmove
    have hpV : p ∈ V := hPV hp
    have hsingleNe : ⁅V,zpowers a⁆ ≠ ⊥ := by
      intro hbot
      have hmem := commutator_mem_commutator (mem_zpowers a) hpV
      rw [commutator_comm (zpowers a), hbot, mem_bot] at hmem
      exact hpne hmem
    have hcard := involution_commutator_card_two_on_elementary_eight V a ⟨hane,ha2⟩
      ((zpowers_le.mpr ha).trans hAV) hV hsingleNe
    have hmeet : ⁅a,p⁆ ∈ ⁅V,zpowers a⁆ ⊓ L := by
      constructor
      · rw [commutator_comm]
        exact commutator_mem_commutator (mem_zpowers a) hpV
      · change ⁅a,p⁆ ∈ ⁅P,A⁆
        rw [commutator_comm]
        exact commutator_mem_commutator ha hp
    have hmeetNe : ⁅V,zpowers a⁆ ⊓ L ≠ ⊥ := by
      intro hbot
      rw [hbot,mem_bot] at hmeet
      exact hpne hmeet
    have heq : ⁅V,zpowers a⁆ ⊓ L = ⁅V,zpowers a⁆ :=
      eq_of_le_of_card_ge inf_le_left (by rw [hcard]; exact (one_lt_card_iff_ne_bot _).mpr hmeetNe)
    exact heq.ge.trans inf_le_right
  have hmoving : ∃ a ∈ A, ∃ p ∈ P, ⁅a,p⁆ ≠ 1 := by
    by_contra! h
    apply hne
    rw [commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
    intro a ha
    rw [mem_centralizer_iff]
    intro p hp
    exact (commutatorElement_eq_one_iff_mul_comm.mp (h a ha p hp)).symm
  obtain ⟨a,ha,p,hp,hap⟩ := hmoving
  have haL := hsmall a ha ⟨p,hp,hap⟩
  have hbound : ⁅V,A⁆ ≤ L := by
    apply commutator_le.mpr
    intro v hv b hb
    by_cases hmove : ∃ q ∈ P, ⁅b,q⁆ ≠ 1
    · exact hsmall b hb hmove (commutator_mem_commutator hv (mem_zpowers b))
    push Not at hmove
    have habmove : ∃ q ∈ P, ⁅a*b,q⁆ ≠ 1 := by
      refine ⟨p,hp,?_⟩
      rw [commutatorElement_mul_left_eq_conj_mul, hmove p hp]
      simpa using hap
    have habL := hsmall (a*b) (A.mul_mem ha hb) habmove
    have hav : ⁅a,v⁆ ∈ L := by
      rw [commutator_comm] at haL
      exact haL (commutator_mem_commutator (mem_zpowers a) hv)
    have habv : ⁅a*b,v⁆ ∈ L := by
      rw [commutator_comm] at habL
      exact habL (commutator_mem_commutator (mem_zpowers (a*b)) hv)
    have hconj : a * ⁅b,v⁆ * a⁻¹ ∈ L := by
      rw [commutatorElement_mul_left_eq_conj_mul] at habv
      exact (L.mul_mem_cancel_right hav).mp habv
    have hbv : ⁅b,v⁆ ∈ L := (mem_normalizer_iff.mp (hnA ha) _).mpr hconj
    rw [← commutatorElement_inv]
    exact L.inv_mem hbv
  exact le_antisymm hbound (commutator_mono hPV le_rfl)

end Subgroup
