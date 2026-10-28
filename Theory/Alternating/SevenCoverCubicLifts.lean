module
public import Theory.Alternating.TripleSevenCubicFacts
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
/-!
# Cubic lifts through the center of an A₇ cover

In a quasisimple group with central quotient A₇ and trivial two-core, an
element whose cube is central has cube one. The odd Schur-cover alternatives
leave the trivial center or the cubic center; in the latter case the
established exponent calculation for the genuine triple cover excludes
order nine. Both cover possibilities and the original central subgroup
are retained.

Source: GLS3, 5.2.3; Aschbacher--Smith, 12.3.12, printed p.811.
-/

public section
open Subgroup Theory.GroupTheory
namespace GLS3.Chapter5.OddCentralCovers

/-- Cubic images have cubic lifts in a quasisimple A₇ cover with trivial two-core. -/
theorem cube_eq_one_of_cube_mem_center {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple Q] (hcore : pCore 2 Q = ⊥)
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin 7))
    (x : Q) (hz : x ^ 3 ∈ center Q) : x ^ 3 = 1 := by
  have ho : Odd (Nat.card (center Q)) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    exact PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot hcore _ le_rfl
  rcases odd_center_alternatives 7 (by decide) e ho with hc | ⟨_,hc⟩
  · have hh : center Q = ⊥ := (eq_bot_iff_card _).mpr hc
    simpa only [hh,mem_bot] using hz
  · have h9 : x ^ 9 = 1 := by
      have hh := (pow_card_eq_one' (x := (⟨x ^ 3,hz⟩ : center Q)))
      rw [hc] at hh
      simpa only [coe_pow,coe_one,←pow_mul] using congrArg Subtype.val hh
    obtain ⟨f⟩ := triple_seven_equiv e hc
    apply f.injective
    simpa only [map_pow,map_one] using
      tripleSeven_cube_eq_one_of_ninth (show (f x) ^ 9 = 1 by
        rw [←map_pow,h9,map_one])
end GLS3.Chapter5.OddCentralCovers
