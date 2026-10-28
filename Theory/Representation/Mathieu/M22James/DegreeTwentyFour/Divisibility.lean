module

public import Theory.Representation.Mathieu.M22James.Uniqueness.Reduction
public import Theory.Representation.BinaryCoprimeDegree
public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Theory.GroupTheory.PGroup.OrderTwentySeven
public import Theory.ElementaryAbelian.Extraspecial

/-!
# Divisibility of arbitrary binary triple-Mathieu modules

A Sylow three-subgroup of the actual triple cover has order twenty-seven.
Central transfer and perfectness force it to be nonabelian, so it is
extraspecial and its center is the cover's center. The central scalar has no
fixed vectors on a faithful irreducible module. Restriction to this actual
extraspecial subgroup therefore makes the binary degree divisible by six.

This is the source-independent form of the Sylow argument in
Aschbacher–Smith H.12.1, printed p.394, also developed for ambient source
actions in ChapterH/Section10To12/TripleDisplacement/SylowStructure and Basic.
It uses neither module recognition nor a specified Schur field.
-/

public section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour
open Subgroup Theory.GroupTheory Representation

private theorem sylow_order (P : Sylow 3 M22TripleCover) :
    Nat.card (P : Subgroup M22TripleCover) = 27 := by
  rw [P.card_eq_multiplicity, M22TripleCover.card]
  rw [show 1330560 = 3 ^ 3 * 49280 by norm_num,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
  simp [Nat.Prime.factorization Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 49280)]

variable {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]

omit [Finite L] [Group.IsPerfect L] in
private theorem center_le_sylow (hc : Nat.card (center L) = 3) (P : Sylow 3 L) :
    center L ≤ (P : Subgroup L) :=
  (IsPGroup.of_card (p := 3) (n := 1)
    (by simpa using hc)).le_sylow_of_normal P

private theorem sylow_nonabelian (hc : Nat.card (center L) = 3) (P : Sylow 3 L) :
    ¬ IsMulCommutative (P : Subgroup L) := by
  have hd : _root_.commutator L = ⊤ := Group.IsPerfect.commutator_eq_top
  have hzderived : center L ≤
      ⁅(P : Subgroup L), (P : Subgroup L)⁆ := by
    intro z hz
    exact center_inf_commutator_inf_sylow_le_commutator P
      ⟨⟨hz, hd ▸ mem_top z⟩, center_le_sylow hc P hz⟩
  intro hcomm
  let := hcomm
  have hbot : ⁅(P : Subgroup L), (P : Subgroup L)⁆ = ⊥ := by
    rw [← map_subtype_commutator, commutator_eq_bot, Subgroup.map_bot]
  have hzbot : center L = ⊥ := le_bot_iff.mp (hbot ▸ hzderived)
  have hc := hc
  rw [hzbot, card_bot] at hc
  omega

private theorem sylow_structure (hc : Nat.card (center L) = 3)
    (P : Sylow 3 L) (hp : Nat.card (P : Subgroup L) = 27) :
    IsExtraspecial 3 (P : Subgroup L) ∧
      (center (P : Subgroup L)).map (P : Subgroup L).subtype =
        center L := by
  have hn := sylow_nonabelian hc P
  have hz := OrderTwentySeven.center_card hp hn
  have hq : Nat.card ((P : Subgroup L) ⧸ center (P : Subgroup L)) = 3 ^ 2 :=
    OrderTwentySeven.quotient_center_card hp hn
  have hnc : ¬ IsCyclic ((P : Subgroup L) ⧸
      center (P : Subgroup L)) := by
    intro h
    let := h
    exact hn (isMulCommutative_of_isCyclic_quotient_center_self (P : Subgroup L))
  have hex : IsExtraspecial 3 (P : Subgroup L) := {
    center_order_p := hz
    quotient_elementary_abelian := {
      toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
      exponent_dvd_p := by
        rw [(not_isCyclic_iff_exponent_eq_prime Nat.prime_three hq).mp hnc] }
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr
      (fun h => hn (center_eq_top_iff.mp h)) }
  have hle : center L ≤
      (center (P : Subgroup L)).map (P : Subgroup L).subtype := by
    intro z hz
    refine ⟨⟨z, center_le_sylow hc P hz⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro p
    exact Subtype.ext (mem_center_iff.mp hz p)
  refine ⟨hex, ?_⟩
  exact (eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective (P : Subgroup L).subtype_injective,
      hz, hc])).symm

/-- Every faithful irreducible binary action of the actual cover has degree
 divisible by six, without any ambient-group or recognition hypothesis. -/
theorem six_dvd_finrank {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) M22TripleCover V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) : 6 ∣ Module.finrank (ZMod 2) V := by
  let P : Sylow 3 M22TripleCover := Classical.choice inferInstance
  obtain ⟨he, hz⟩ := sylow_structure M22TripleCover.center_card P (sylow_order P)
  let := he
  apply BinaryCoprimeDegree.six_dvd_finrank_of_extraspecial_twentySeven
    (ρ.comp (P : Subgroup M22TripleCover).subtype) (sylow_order P)
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  apply (Uniqueness.scalar_fixed_iff ρ hf v).mp
  have hs : scalar ∈ (center (P : Subgroup M22TripleCover)).map
      (P : Subgroup M22TripleCover).subtype := hz.symm ▸ scalar_mem_center
  obtain ⟨z, hz, hzs⟩ := hs
  have h := (Representation.mem_invariants _ v).mp hv ⟨z, hz⟩
  change ρ (z : M22TripleCover) v = v at h
  change (z : M22TripleCover) = scalar at hzs
  rwa [hzs] at h

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour
