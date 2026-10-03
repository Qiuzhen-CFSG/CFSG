module

public import Stellmacher.SectionsOneToFourDefs
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Transporting an offender into a specified Sylow subgroup

An arbitrary nontrivial elementary two-subgroup whose fixed-point cardinality
satisfies the offender bound has a conjugate in any prescribed Sylow
two-subgroup. The action of the conjugating element identifies the two fixed
subgroups, so the conjugate has the same measure and lies in the canonical
offender join. The involution wrapper replaces the actor cardinality by two.

These are the final transport steps for the representation argument in
Stellmacher (9.1)(8), printed p.47 / PDF p.37 of
`refs/files/stellmacher-n-group.pdf`. They do not assume canonical generation,
a wreath model, or that an arbitrary elementary four is itself an offender.
-/

namespace Stellmacher.SectionOne

universe u

private theorem offender_fixedPoints_conjugate
    {K V : Type u} [Group K] [Group V] [MulDistribMulAction K V]
    (actor : Subgroup K) (element : K) :
    FixedPoints.subgroup (actor.conjBy element) V =
      (FixedPoints.subgroup actor V).map
        (MulDistribMulAction.toMulAut K V element).toMonoidHom := by
  ext vector
  constructor
  · intro hvector
    refine ⟨element⁻¹ • vector, ?_, by simp⟩
    change element⁻¹ • vector ∈ FixedPoints.subgroup actor V
    rw [FixedPoints.mem_subgroup]
    intro member
    change (member : K) • (element⁻¹ • vector) = element⁻¹ • vector
    have hfix := (FixedPoints.mem_subgroup
      (M := actor.conjBy element) (a := vector)).mp hvector
      ⟨element * (member : K) * element⁻¹, Subgroup.mem_map_of_mem
        (MulAut.conj element).toMonoidHom member.property⟩
    change (element * (member : K) * element⁻¹) • vector = vector at hfix
    simpa [mul_smul] using congrArg (fun value : V => element⁻¹ • value) hfix
  · rintro ⟨vector, hvector, rfl⟩
    rw [FixedPoints.mem_subgroup]
    rintro ⟨member, source, hsource, rfl⟩
    have hfix := (FixedPoints.mem_subgroup (M := actor) (a := vector)).mp hvector
      ⟨source, hsource⟩
    change (element * source * element⁻¹) • (element • vector) = element • vector
    simpa [mul_smul] using congrArg (fun value : V => element • value) hfix

public theorem oneJ_ne_bot_of_elementary_card_bound
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [MulDistribMulAction K V]
    (sylow : Sylow 2 K) (actor : Subgroup K)
    (helementary : IsElementaryAbelian 2 actor) (hnontrivial : actor ≠ ⊥)
    (hbound : Nat.card V ≤ Nat.card (FixedPoints.subgroup actor V) * Nat.card actor) :
    oneJ (V := V) (sylow : Subgroup K) ≠ ⊥ := by
  let _ : IsElementaryAbelian 2 actor := helementary
  obtain ⟨other, hother⟩ := (IsElementaryAbelian.isPGroup (p := 2) (G := actor)).exists_le_sylow
  obtain ⟨element, helement⟩ := MulAction.exists_smul_eq K other sylow
  let conjugate := actor.conjBy element
  have hle : conjugate ≤ (sylow : Subgroup K) := by
    rw [← helement]
    exact Subgroup.map_mono hother
  have hcard : Nat.card conjugate = Nat.card actor :=
    Subgroup.card_map_of_injective (MulAut.conj element).injective
  have hfixed : Nat.card (FixedPoints.subgroup conjugate V) =
      Nat.card (FixedPoints.subgroup actor V) := by
    rw [show conjugate = actor.conjBy element from rfl, offender_fixedPoints_conjugate]
    exact Subgroup.card_map_of_injective
      (MulDistribMulAction.toMulAut K V element).injective
  have honeA : oneA (V := V) (sylow : Subgroup K) conjugate := by
    refine ⟨hle, IsElementaryAbelian.map (MulAut.conj element).toMonoidHom, ?_⟩
    unfold m
    rw [hcard, hfixed]
    have hpos : (0 : ℚ) < (Nat.card (FixedPoints.subgroup actor V) : ℚ) *
        (Nat.card actor : ℚ) := mul_pos (Nat.cast_pos.mpr Nat.card_pos)
          (Nat.cast_pos.mpr Nat.card_pos)
    apply (div_le_one hpos).mpr
    exact_mod_cast hbound
  have hconjugate : conjugate ≠ ⊥ := by
    intro hbot
    have hone := Subgroup.one_lt_card_iff_ne_bot actor |>.mpr hnontrivial
    rw [← hcard, hbot, Subgroup.card_bot] at hone
    omega
  intro hbot
  apply hconjugate
  apply le_antisymm _ bot_le
  have hjoin : conjugate ≤ oneJ (V := V) (sylow : Subgroup K) := le_sSup honeA
  exact hjoin.trans hbot.le

public theorem oneJ_ne_bot_of_involution_fixed_card_bound
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [MulDistribMulAction K V]
    (sylow : Sylow 2 K) (actor : K) (hsquare : actor ^ 2 = 1)
    (hnontrivial : actor ≠ 1)
    (hbound : Nat.card V ≤ 2 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers actor) V)) :
    oneJ (V := V) (sylow : Subgroup K) ≠ ⊥ := by
  have hcard : Nat.card (Subgroup.zpowers actor) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hsquare hnontrivial]
  apply oneJ_ne_bot_of_elementary_card_bound sylow (Subgroup.zpowers actor)
    (IsElementaryAbelian.zpowers_of_pow_eq_one hsquare)
  · intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  · simpa [hcard, Nat.mul_comm] using hbound


end Stellmacher.SectionOne
