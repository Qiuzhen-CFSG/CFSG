module

public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Elementary central quotients with cyclic center

If a group has elementary abelian central quotient of exponent two, its
commutators are central involutions. When its center is finite cyclic and
the group is nonabelian, the derived subgroup therefore has order two.

The commutator calculation uses the centrality of squares. The kernel of
squaring on the center contains the derived subgroup and is cyclic of
exponent at most two. This is the first reduction in Gorenstein,
*Finite Groups*, Lemma 5.4.7, pp. 196–197.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace IsElementaryAbelian

/-- Squares are central when the central quotient has exponent two. -/
public theorem sq_mem_center_of_central_quotient
    {Q : Type*} [Group Q] (hquot : IsElementaryAbelian 2 (Q ⧸ center Q)) (x : Q) :
    x ^ 2 ∈ center Q := by
  let _ := hquot
  apply (QuotientGroup.eq_one_iff (N := center Q) _).mp
  change QuotientGroup.mk' (center Q) (x ^ 2) = 1
  rw [map_pow]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (Q ⧸ center Q)) _

/-- Commutators are central when the central quotient is elementary abelian. -/
public theorem commutator_le_center_of_central_quotient
    {p : ℕ} {Q : Type*} [Group Q]
    (hquot : IsElementaryAbelian p (Q ⧸ center Q)) :
    _root_.commutator Q ≤ center Q := by
  let _ := hquot
  exact Normal.quotient_commutative_iff_commutator_le.mp inferInstance

/-- Every commutator has square one when the central quotient has exponent two. -/
public theorem commutatorElement_sq_eq_one_of_central_quotient
    {Q : Type*} [Group Q] (hquot : IsElementaryAbelian 2 (Q ⧸ center Q)) (x y : Q) :
    ⁅x, y⁆ ^ 2 = 1 := by
  have hc : ⁅x, y⁆ ∈ center Q := hquot.commutator_le_center_of_central_quotient
    (commutator_mem_commutator (mem_top x) (mem_top y))
  have hsq : ⁅x ^ 2, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_center_iff.mp (hquot.sq_mem_center_of_central_quotient x) y).symm
  rw [pow_two, commutatorElement_mul_left_eq_conj_mul,
    mem_center_iff.mp hc x, mul_inv_cancel_right, ← pow_two] at hsq
  exact hsq

/-- In the cyclic-center case the derived subgroup has order dividing two. -/
public theorem card_commutator_dvd_two_of_cyclic_center
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic (center Q)]
    (hquot : IsElementaryAbelian 2 (Q ⧸ center Q)) :
    Nat.card (_root_.commutator Q) ∣ 2 := by
  let square : center Q →* center Q := powMonoidHom 2
  let K : Subgroup Q := square.ker.map (center Q).subtype
  have hle : _root_.commutator Q ≤ K := by
    apply commutator_le.mpr
    intro x _ y _
    refine ⟨⟨⁅x, y⁆, hquot.commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top x) (mem_top y))⟩, ?_, rfl⟩
    change (⟨⁅x, y⁆, _⟩ : center Q) ^ 2 = 1
    exact Subtype.ext (hquot.commutatorElement_sq_eq_one_of_central_quotient x y)
  have hKcentral : K ≤ center Q := map_subtype_le _
  let : IsCyclic K := isCyclic_of_injective (inclusion hKcentral)
    (inclusion_injective hKcentral)
  have hKexp : Monoid.exponent K ∣ 2 := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨x, z, hz, rfl⟩
    apply Subtype.ext
    exact congrArg (fun a : center Q => (a : Q)) (show z ^ 2 = 1 from hz)
  rw [IsCyclic.exponent_eq_card] at hKexp
  exact (card_dvd_of_le hle).trans hKexp

/-- A nonabelian group with cyclic center and elementary binary central
quotient has derived subgroup of order two. -/
public theorem card_commutator_eq_two_of_cyclic_center
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic (center Q)]
    (hquot : IsElementaryAbelian 2 (Q ⧸ center Q)) (hnonab : center Q ≠ ⊤) :
    Nat.card (_root_.commutator Q) = 2 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp
    hquot.card_commutator_dvd_two_of_cyclic_center with h | h
  · exact (hnonab ((commutator_eq_bot_iff_center_eq_top Q).mp
      ((card_eq_one.mp h)))).elim
  · exact h

/-- The center has nontrivial image in the abelianization unless the
nonabelian group already has center of order two. -/
public theorem center_image_abelianization_ne_bot
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic (center Q)]
    (hquot : IsElementaryAbelian 2 (Q ⧸ center Q)) (hnonab : center Q ≠ ⊤)
    (hcenter : Nat.card (center Q) ≠ 2) :
    (center Q).map (QuotientGroup.mk' (_root_.commutator Q)) ≠ ⊥ := by
  intro hbot
  have hle : center Q ≤ _root_.commutator Q := by
    simpa only [QuotientGroup.ker_mk'] using ((map_eq_bot_iff (center Q)).mp hbot)
  have heq := le_antisymm hle hquot.commutator_le_center_of_central_quotient
  exact hcenter (heq ▸ hquot.card_commutator_eq_two_of_cyclic_center hnonab)

/-- Modding the abelianization by the center image still gives an
elementary abelian group of exponent two. -/
public theorem abelianization_quotient_center_image
    {Q : Type*} [Group Q] (hquot : IsElementaryAbelian 2 (Q ⧸ center Q)) :
    IsElementaryAbelian 2
      ((Q ⧸ _root_.commutator Q) ⧸
        (center Q).map (QuotientGroup.mk' (_root_.commutator Q))) := by
  let : IsMulCommutative (Q ⧸ _root_.commutator Q) :=
    Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction x using QuotientGroup.induction_on with
    | H x =>
      apply (QuotientGroup.eq_one_iff _).mpr
      exact mem_map_of_mem (QuotientGroup.mk' (_root_.commutator Q))
        (hquot.sq_mem_center_of_central_quotient x)

/-- Every subgroup inherits an elementary binary central quotient. -/
public theorem central_quotient_subgroup {Q : Type*} [Group Q]
    (hquot : IsElementaryAbelian 2 (Q ⧸ center Q)) (F : Subgroup Q) :
    IsElementaryAbelian 2 (F ⧸ center F) := by
  have hcomm : _root_.commutator F ≤ center F := by
    apply commutator_le.mpr
    intro x _ y _
    apply mem_center_iff.mpr
    intro z
    apply Subtype.ext
    exact mem_center_iff.mp
      (hquot.commutator_le_center_of_central_quotient
        (commutator_mem_commutator (mem_top (x : Q)) (mem_top (y : Q)))) z
  refine {
    toIsMulCommutative := Normal.quotient_commutative_iff_commutator_le.mpr hcomm
    exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    change QuotientGroup.mk' (center F) x ^ 2 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp
      (hquot.sq_mem_center_of_central_quotient (x : Q)) y)

end IsElementaryAbelian
