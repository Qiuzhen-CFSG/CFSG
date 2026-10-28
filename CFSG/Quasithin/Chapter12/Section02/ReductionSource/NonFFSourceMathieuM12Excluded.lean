module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM12
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM12Sixteen

/-!
# The original M12 branch is impossible

The literal source orbit has r = 6, w = 2 and automizer two-rank four.
Every elementary sixteen on its actual full automizer fixes at most three
heart dimensions, while its element-fixed spaces span at least eight.
The reverse-offender equality then contradicts these dimensions, exactly
as in source 7.5.4. The native pair calculation supplies the terminal bounds
without an outer centralizer-table assumption.

This excludes the M12 alternative in the normalized Mathieu disjunction.
The M22, M23 and M24 branches and final J4 assembly remain separate.
Source: Aschbacher--Smith 7.5.4, printed p.700; H.11.1(4), pp.392--393.
-/
public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- Source 7.5.4 excludes the M12 quotient on the original non-FF chosen orbit. -/
theorem sourceOrbit_not_m12_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ¬ Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M12) := by
  intro hq
  obtain ⟨hc⟩ := D.sourceOrbit_m12_automizer_marking h.toHypothesis1221
    (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq
  obtain ⟨hw,hrank,hr,hm⟩ := D.sourceOrbit_m12_parameters h hmany hV hq hnon
  apply Chapter7.m12_exclusion_of_fixedSpace_bounds D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon)
    (le_of_eq hrank) (le_of_eq hw) (ge_of_eq hr) (by rw [hm]; decide)
    (hc.finrank_eq_ten _)
  intro I hI hrank
  let := hI
  have hcI : Nat.card I = 16 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 I).exists_card_eq
    have hn4 : n = 4 := by simpa only [rank,hn,Nat.log_pow Nat.one_lt_two] using hrank
    rw [hn,hn4]; rfl
  exact MathieuM12Sixteen.dimensions_marked _ hc I hcI

/-- The source Mathieu disjunction loses its M12 branch on the original orbit. -/
theorem sourceOrbit_mathieu_remaining_quotients_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24) :=
  hm.resolve_left (D.sourceOrbit_not_m12_of_many h hmany hV hnon)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
