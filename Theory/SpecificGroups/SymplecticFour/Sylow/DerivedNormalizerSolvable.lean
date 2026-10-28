module

public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Solvable Sylow two-normalizers in Sp₄(2ⁿ)′

Every Sylow two-normalizer in the commutator subgroup of the native
symplectic four-space matrix group is solvable. Over a nonbinary field,
perfectness identifies the derived carrier with the full group, whose
Sylow normalizers are the solvable flag Borels. Over a two-element field,
the explicit equivalence with A₆ makes each Sylow two-subgroup
self-normalizing. Both identifications transport actual Sylow subgroups
and their normalizers.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
`refs/quasithin.pdf`, B.4.2, printed p.86; B.5.5(1)(iv), pp.104–105;
and the Borel in the proof of 15.3.49(k), p.1144. This is the individual
derived symplectic factor calculation; the commuting-component closure
assembly is a separate consumer.
-/

public section

open Subgroup

namespace Theory.SpecificGroups.SymplecticFour

variable {F : Type*} [Field F] [Finite F]

/-- Sylow two-normalizers are solvable on the exact commutator-of-Sp₄ carrier,
including the binary endpoint. -/
theorem isSolvable_derived_sylow_normalizer {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (commutator (Sp F))) :
    Group.IsSolvable (normalizer (S : Set (commutator (Sp F)))) := by
  by_cases htwo : Nat.card F = 2
  · rw [derived_sylow_normalizer_eq_of_card_two htwo]
    let _ := S.isPGroup'.isNilpotent
    infer_instance
  · have hn2 : 2 ≤ n := by
      by_contra h
      have he : n = 1 := by omega
      simp [he] at hF
      exact htwo hF
    have hq : 2 < Nat.card F := by
      rw [hF]
      have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn2
      norm_num at h ⊢
      omega
    let _ := Fintype.ofFinite F
    let _ : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let e := derivedEquivFull_of_card_gt_two hq
    exact Sylow.isSolvable_normalizer_of_surjective e.symm.toMonoidHom e.symm.surjective
      (isSolvable_sylow_normalizer hF hn) S

/-- Transport through an actual equivalence with the derived symplectic model. -/
theorem isSolvable_derived_sylow_normalizer_of_equiv
    {Q : Type*} [Group Q] [Finite Q] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (e : Q ≃* commutator (Sp F))
    (S : Sylow 2 Q) : Group.IsSolvable (normalizer (S : Set Q)) :=
  Sylow.isSolvable_normalizer_of_surjective e.symm.toMonoidHom e.symm.surjective
    (isSolvable_derived_sylow_normalizer hF hn) S

end Theory.SpecificGroups.SymplecticFour
