module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.OddLinear.Inner
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import Theory.SpecificGroups.PSL3Three.InnerInvolutionCentralizer
public import Theory.SpecificGroups.GL2.ThreeSolvable

/-!
# Odd-linear component preliminaries

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
of 1 March 2004, (E2)(ii) and 16.1.2, 16.1.5–7, printed pp.1170–1172.

The full PSL₂ alternatives have trivial center. Perfection excludes parameter
three, leaving primes at least five. The prime-field automorphism calculation
proves Sylow-fixer innerness without any restriction on automorphism order.
The inner involution centralizers are Sylow two-subgroups for PSL₂, and GL₂(3)
for PSL₃(3); their solvability rules out components.

The outer fixed-subgroup tables and the PSL₃(3) Sylow-fixer assertion remain
separate obligations. No automorphism standardness is assumed by the results
here, and no result about the full 16.1.5 table is asserted.
-/

public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.OddLinear

open Subgroup Theory.GroupTheory
open scoped MatrixGroups

variable {L : Type*} [Group L]

/-- The full PSL₂ alternative of (E2)(ii) has trivial center. -/
theorem pslTwo_center_eq_bot {q : ℕ} (hL : ClassicalGroup.IsPSL L 2 q) :
    center L = ⊥ := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hL
  apply (center L).eq_bot_iff_card.mpr
  calc
    Nat.card (center L) = Nat.card (center PSL(2,F)) :=
      Nat.card_congr (centerCongr e).toEquiv
    _ = 1 := (center PSL(2,F)).eq_bot_iff_card.mp (GorensteinWalter.psl2_center_eq_bot F)

/-- Parameter three is incompatible with the source's perfection hypothesis. -/
theorem pslTwo_not_three [Group.IsPerfect L] (hL : ClassicalGroup.IsPSL L 2 3) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three hF
    (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

/-- The Fermat–Mersenne parameter in (E2)(ii) is at least five for a component.
The source's quasisimplicity supplies the perfection used here. -/
theorem pslTwo_parameter_ge_five [Group.IsPerfect L] {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hL : ClassicalGroup.IsPSL L 2 p) : 5 ≤ p := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases hp.2 with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hh : 2 ≤ 2 ^ (2 ^ k) := Nat.le_pow (by positivity)
      omega
    · have hk0 : k ≠ 0 := by intro he; simp [he] at hk
      have hh := dvd_pow_self 2 hk0
      rw [← hk] at hh
      norm_num at hh
  have hp3 : p ≠ 3 := fun h => pslTwo_not_three (h ▸ hL)
  have ho : Odd p := hp.1.odd_of_ne_two hp2
  have hmin := hp.1.two_le
  obtain ⟨k, hk⟩ := ho
  omega

/-- The PSL₂ prime-field cases of 16.1.6, including primes five and seven
and every power-of-two automorphism order. -/
theorem pslTwo_sylow_centralizing_two_automorphisms {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hlarge : 3 < p) :
    HasInnerSylowCentralizingTwoAutomorphisms PSL(2, ZMod p) := by
  intro r _ S _ hS
  obtain ⟨g, _, hg⟩ := Theory.PSL2.primeField_sylow_fixed_inner hp hlarge S r hS
  exact ⟨g, hg⟩

/-- The actual GL₂(3) fixed subgroup in the inner case of 16.1.5(1) is solvable. -/
theorem pslThree_inner_involution_solvable (r : MulAut Matrix.PSL3Three.PSL)
    (hr : orderOf r = 2) (hi : ∃ g, r = MulAut.conj g) :
    Group.IsSolvable r.fixedSubgroup := by
  let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
    Matrix.GeneralLinearGroup.three_isSolvable
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Matrix.PSL3Three.innerInvolutoryAutFixedEquiv r hr hi).toMonoidHom)
    (Matrix.PSL3Three.innerInvolutoryAutFixedEquiv r hr hi).injective

private theorem no_component_of_solvable {G : Type*} [Group G] [Group.IsSolvable G]
    (K : Subgroup G) : ¬ IsComponent G K := by
  intro hK
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  exact Group.IsPerfect.not_isSolvable K inferInstance

/-- No component occurs in an inner PSL₃(3) involution centralizer. -/
theorem pslThree_inner_involution_no_component (r : MulAut Matrix.PSL3Three.PSL)
    (hr : orderOf r = 2) (hi : ∃ g, r = MulAut.conj g)
    (K : Subgroup r.fixedSubgroup) : ¬ IsComponent r.fixedSubgroup K := by
  let : Group.IsSolvable r.fixedSubgroup := pslThree_inner_involution_solvable r hr hi
  exact no_component_of_solvable K

/-- No component occurs in an inner Fermat–Mersenne PSL₂ involution centralizer. -/
theorem pslTwo_inner_involution_no_component {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hF : Nat.card F = p) (hp : IsFermatOrMersennePrime p) (hp5 : 5 ≤ p)
    (r : MulAut PSL(2,F)) (hr : orderOf r = 2)
    (hi : ∃ g : PSL(2,F), r = MulAut.conj g) (K : Subgroup r.fixedSubgroup) :
    ¬ IsComponent r.fixedSubgroup K := by
  let : Group.IsSolvable r.fixedSubgroup := pslTwo_inner_involution_solvable hF hp hp5 r hr hi
  exact no_component_of_solvable K

end CFSG.Quasithin.Chapter16.OtherPreliminaries.OddLinear
