module

public import Theory.GroupAction.ElementaryEightTwoActionFixedLine
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The center determined by a central commutator line

Let D be a normal elementary abelian subgroup of order eight in a group of
order thirty-two. If the derived subgroup lies in D and in the center, and
D intersects the center in order two, then D is self-centralizing and the
full center has order two.

Central commutators have exponent two, so every square is central. The
conjugation image on D is therefore elementary abelian. Its common fixed
subgroup is the supplied intersection with the center; the elementary-eight
fixed-line theorem gives image order four. Counting the conjugation kernel
then identifies it with D, forcing the center into D.

This is the center-control step in the elementary-eight supplement argument
for Stellmacher (8.6)(a2), Journal of Algebra 190 (1997), pp.41--42. It does
not assume a second elementary eight or an extraspecial classification.
-/

open scoped commutatorElement IsMulCommutative

namespace Subgroup

public theorem square_mem_center_of_elementary_central_commutator
    {G : Type*} [Group G] (D : Subgroup G) (hD : IsElementaryAbelian 2 D)
    (hderived : _root_.commutator G ≤ D ⊓ center G) (element : G) :
    element ^ 2 ∈ center G := by
  let := hD
  apply mem_center_iff.mpr
  intro other
  have hmem := hderived (commutator_mem_commutator
    (mem_top element) (mem_top other))
  have hcomm := mem_center_iff.mp hmem.2 element
  have hpow := elemPow_eq_one_of_isElementaryAbelian (p := 2) ⁅element, other⁆ hmem.1
  have hbracket : ⁅element ^ 2, other⁆ = 1 := by
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hcomm]
    simpa only [mul_inv_cancel_right, ← pow_two] using hpow
  exact (commutatorElement_eq_one_iff_mul_comm.mp hbracket).symm

public theorem centralizer_eq_and_center_card_two_of_central_commutator
    {G : Type*} [Group G] [Finite G] (D : Subgroup G) [D.Normal]
    (hD : IsElementaryAbelian 2 D) (hDcard : Nat.card D = 8)
    (hGcard : Nat.card G = 32)
    (hderived : _root_.commutator G ≤ D ⊓ center G)
    (hfixed : Nat.card (D ⊓ center G : Subgroup G) = 2) :
    centralizer (D : Set G) = D ∧ Nat.card (center G) = 2 := by
  classical
  let := hD
  let action : G →* MulAut D := MulAut.conjNormal
  have hker : action.ker = centralizer (D : Set G) := by
    ext element
    rw [MonoidHom.mem_ker]
    constructor
    · intro h member hmember
      have hfix := congrArg (fun automorphism : MulAut D =>
        (automorphism ⟨member, hmember⟩ : G)) h
      change element * member * element⁻¹ = member at hfix
      calc
        member * element = (element * member * element⁻¹) * element := by rw [hfix]
        _ = element * member := by simp [mul_assoc]
    · intro h
      ext member
      change element * (member : G) * element⁻¹ = member
      rw [← h member member.property]
      simp [mul_assoc]
  have hsquare (element : G) : action element ^ 2 = 1 := by
    rw [← map_pow]
    apply (MonoidHom.mem_ker).mp
    rw [hker]
    exact center_le_centralizer _
      (square_mem_center_of_elementary_central_commutator D hD hderived element)
  have hrangePow (automorphism : action.range) : automorphism ^ 2 = 1 := by
    apply Subtype.ext
    obtain ⟨element, helement⟩ := automorphism.property
    change (automorphism : MulAut D) ^ 2 = 1
    rw [← helement]
    exact hsquare element
  let : IsElementaryAbelian 2 action.range := {
    toIsMulCommutative := ⟨⟨fun left right =>
      (Commute.of_orderOf_dvd_two (fun element =>
        orderOf_dvd_of_pow_eq_one (hrangePow element)) left right).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hrangePow }
  have hfixeq : (FixedPoints.subgroup action.range D).map D.subtype =
      D ⊓ center G := by
    ext element
    constructor
    · rintro ⟨member, hmember, rfl⟩
      refine ⟨member.property, mem_center_iff.mpr ?_⟩
      intro other
      have hfix := congrArg Subtype.val (hmember ⟨action other, ⟨other, rfl⟩⟩)
      change other * (member : G) * other⁻¹ = member at hfix
      calc
        other * (member : G) = (other * member * other⁻¹) * other := by
          simp [mul_assoc]
        _ = (member : G) * other := by rw [hfix]
    · intro helement
      refine ⟨⟨element, helement.1⟩, ?_, rfl⟩
      intro automorphism
      obtain ⟨other, hother⟩ := automorphism.property
      apply Subtype.ext
      change ((automorphism : MulAut D) ⟨element, helement.1⟩ : G) = element
      rw [← hother]
      change other * element * other⁻¹ = element
      rw [mem_center_iff.mp helement.2 other]
      simp [mul_assoc]
  have hfixcard : Nat.card (FixedPoints.subgroup action.range D) = 2 := by
    rw [← card_map_of_injective D.subtype_injective, hfixeq, hfixed]
  have hactioncard := (elementaryEight_two_action_fixed_line hDcard action.range hfixcard).1
  have hkercard : Nat.card action.ker = 8 := by
    have hcount := action.ker.card_mul_index
    rw [index_ker, hactioncard, hGcard] at hcount
    omega
  have hDker : D ≤ action.ker := by
    rw [hker]
    intro element helement member hmember
    exact congrArg Subtype.val (mul_comm (⟨member, hmember⟩ : D) ⟨element, helement⟩)
  have heq : action.ker = D := (eq_of_le_of_card_ge hDker (by omega)).symm
  have hcent : center G ≤ D := by
    rw [← heq, hker]
    exact center_le_centralizer _
  exact ⟨hker.symm.trans heq, by simpa only [inf_eq_right.mpr hcent] using hfixed⟩

end Subgroup

