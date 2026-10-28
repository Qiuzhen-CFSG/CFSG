module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.SingleOffender

/-!
# The support of a normal cubic moved by offenders

In a faithful solvable binary FF action with trivial two-core, a normal
subgroup of order three moved by the offender subgroup is moved by one
best offender. B.1.8 identifies it with one natural factor's odd core.
Its moved subspace consequently has at most four elements.

This is the support bound used in the solvable comparison in original
13.2.12, printed p.882. The original-point consumer retains the literal
centralizer quotient and supplies both cubic order and offender movement.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem normal_cubic_moved_card_le_four
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) (hff : IsFFModule ρ)
    (K : Subgroup G) [K.Normal] (hc : Nat.card K = 3)
    (hm : ¬ offenderSubgroup ρ ≤ centralizer (K : Set G)) :
    Nat.card (subspaceCommutator ρ ⊤ K) ≤ 4 := by
  obtain ⟨d⟩ := solvableFFStructure_nonempty ρ hsolv hcore hfaith hff
  have hex : ∃ A, IsBestOffender ρ A ∧ ¬ A ≤ centralizer (K : Set G) := by
    by_contra! hn
    apply hm
    exact iSup_le fun A => iSup_le fun hA => hn A hA.1
  obtain ⟨A,hA,hn⟩ := hex
  have hcomm : K = ⁅K,A⁆ := by
    have hle : ⁅K,A⁆ ≤ K := commutator_le_left K A
    have hdiv := card_dvd_of_le hle
    rw [hc] at hdiv
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hh | hh
    · have hb : ⁅K,A⁆ = ⊥ := card_eq_one.mp hh
      exact (hn (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))).elim
    · exact (eq_of_le_of_card_ge hle (by rw [hh,hc])).symm
  obtain ⟨i,hi⟩ := ThreeConjugates.single_best_three_coordinate d K A hc hA hcomm
  have hle : K ≤ d.factor i := hi ▸ d.toSolvableFFFactors.factorOddCore_le i
  have hsub : subspaceCommutator ρ ⊤ K ≤ subspaceCommutator ρ ⊤ (d.factor i) := by
    apply Submodule.span_mono
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact ⟨g,hle hg,v,hv,rfl⟩
  have hdim := Submodule.finrank_mono hsub
  rw [d.toSolvableFFFactors.support_finrank] at hdim
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hdim).trans_eq rfl
end CFSG.Quasithin.ChapterB
