module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNoncentralExclusion

/-!
# Omega centralization from an actual local Cartan escape

The original local escape reduction leaves the exceptional component or a
binary-triality container. The exceptional component already centralizes
the original Sylow omega-center. Baumann control gives the same centralization
for the binary-triality container, without excluding that ambient case.
In both cases the actual residual lies in the container, and its Sylow
supplement therefore places all of H in the original omega centralizer.

This consequence needs neither the complete 5.1.13 classification nor its
binary-triality exclusion. All hypotheses concern the original Input,
H-star subgroup, compatible Cartan pair and actual local overgroup.
Source: Aschbacher–Smith 5.1.13, printed pp.635–638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- Every actual local Cartan escape makes the original H centralize
the full omega-center of the original Sylow subgroup. -/
theorem omegaCentralizer_of_local_cartan_escape
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    H ≤ omegaCentralizer T := by
  apply (residual_le_omegaCentralizer_iff hH.1.1.2).mp
  rcases localCartan_escape_binary_or_exceptional h hH hgen c hY hescape with
    ⟨_, _, _, X, hRX, hXC, _⟩ |
    ⟨K, hKH, _, _, hKT, hKL, hR, C, hC, _, hKC, _, _, _, _, hKR, hbin⟩
  · exact hRX.trans hXC
  · obtain ⟨_, _, hm, _⟩ := hbin
    exact (hKR ▸ hKC).trans
      (BinaryOmega.original_container_centralizes h hH c hKH hKL hKT hR
        hY hescape C hC hKC hm)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
