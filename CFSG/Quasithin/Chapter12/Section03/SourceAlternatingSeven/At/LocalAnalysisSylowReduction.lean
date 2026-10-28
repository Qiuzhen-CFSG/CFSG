module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowReduction
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisFusion
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNormalizer

/-!
# LocalAnalysisSylowReduction at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowReduction`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer

theorem points_nonempty_at (E : S.NaturalCoordinates) (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    Nonempty (Points E) := by
  obtain ⟨x,hx,hxc⟩ := E.central_representative_weight_at structural (n := 2) (Or.inl rfl)
  obtain ⟨y,hy,hyc⟩ := E.central_representative_weight_at structural (n := 6) (Or.inr (Or.inr rfl))
  exact ⟨⟨x,y,hx,hy,hxc,hyc⟩⟩

lemma controlsFusion_of_omega_action_at {P : Points E} (M : P.Models) (R : P.AmbientResiduals)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hmove : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) →
      ∃ g ∈ normalizer (T : Set G), g*(P.two:G)*g⁻¹=P.six)
    (x y : G) (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : ∃ g : G, g*x*g⁻¹=y) : ∃ l ∈ L, l*x*l⁻¹=y :=
  E.controlsFusion_at structural (normalizer_le_of_omega_action M R hmove) x y hx hy hx1 hy1 hxy

end SylowNormalizer

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

