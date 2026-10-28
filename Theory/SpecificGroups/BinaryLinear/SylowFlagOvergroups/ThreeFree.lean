module
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.Covers
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.CubicResidual

/-!
# Three-free overgroups of a binary linear Sylow subgroup

Every overgroup of the full binary flag stabilizer is the stabilizer of a
partial flag. Omitting a cut includes the corresponding minimal parabolic.
Its cubic residual supplements the full flag group; if three does not divide
the overgroup's order, that residual is trivial, contradicting the strict
cover relation. Thus no cut is omitted and the overgroup is the Sylow itself.

This argument applies in arbitrary binary dimension. The actual SL₄(2) and
SL₅(2) source consumers exclude the original quintic actor in
Aschbacher--Smith 15.1.22(7), printed pp.1099--1100. The flag-overgroup
result is the binary specialization of the parabolic geometry cited there
from Aschbacher, Finite Group Theory (1986), 47.7.
-/

public section
open Subgroup
namespace BinaryLinear.SylowFlagOvergroups
open OuterCyclic InvariantNodeActions OrderedResidualConjugators

/-- A binary linear Sylow overgroup of order prime to three is the Sylow itself. -/
theorem eq_sylow_of_not_three_dvd {m : ℕ}
    (S : Sylow 2 (LinearGroup (m+1))) (H : Subgroup (LinearGroup (m+1)))
    (hSH : (S : Subgroup _) ≤ H) (h3 : ¬3 ∣ Nat.card H) : H = S := by
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1))) DFunLike.coe_injective
  obtain ⟨b,cuts,hS,hH⟩ := exists_flag_of_sylow_le S H hSH
  have hall : cuts = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    by_contra hi
    have hPH : minimalParabolic b i ≤ H := by
      rw [hH]
      exact (cutStabilizer_le_iff b _ _).mpr (fun j hj he => hi (he ▸ hj))
    have hp3 : Nat.Coprime 3 (Nat.card (minimalParabolic b i)) :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr h3).of_dvd_right (card_dvd_of_le hPH)
    have hr : primeToResidual 3 (minimalParabolic b i) = ⊥ := by
      apply bot_unique
      apply primeToResidual_le
      simpa only [index_bot] using hp3
    have he := minimalParabolic_cubic_supplement b i
    rw [hr,Subgroup.map_bot,bot_sup_eq,←hS] at he
    exact (fullFlag_covBy_minimalParabolic S b hS i).ne he.symm
  rw [hH,hall,←hS]

end BinaryLinear.SylowFlagOvergroups
