module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.M12Exclusion
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.M22Exclusion

/-!
# Normalized Mathieu Hall faithfulness

The literal Hall kernel is trivial for all four original Mathieu central
quotients. M₁₂ and M₂₂ are excluded by the original non-FF action and the native
Thompson-normalizer comparison. M₂₃ and M₂₄ are already excluded by the full
residual/core comparison. The assembly retains the original ambient Sylow,
chosen module, covering centers, and section-conjugation kernel.

This proves the normalized Mathieu instance of Aschbacher–Smith 4.4.14,
printed pp.624–625, with the source hypotheses recorded in Inputs.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Subgroup
universe u

/-- The original normalized Mathieu Hall-faithfulness contract, with no
additional residual, normalizer, model, or representation premises. -/
theorem sourceMathieuHallFaithfulAt {G : Type u} [Group G] [Finite G]
    (T : Sylow 2 G) : SourceMathieuHallFaithfulAt T := by
  intro L V D h hmany hV _ hm hnon H hH hlarge B hBN hHall _ _
  rcases hm with hm | hm | hm | hm
  · exact D.sourceOrbit_m12_hall_faithful h hmany hV hm hnon hH hlarge B hBN hHall
  · exact D.sourceOrbit_m22_hall_faithful h hmany hV hm hnon hH hlarge B hBN hHall
  · exact D.sourceOrbit_inner_mathieu_hall_faithful h hmany hV (.inl hm) hnon hH hlarge B hBN hHall
  · exact D.sourceOrbit_inner_mathieu_hall_faithful h hmany hV (.inr hm) hnon hH hlarge B hBN hHall
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
