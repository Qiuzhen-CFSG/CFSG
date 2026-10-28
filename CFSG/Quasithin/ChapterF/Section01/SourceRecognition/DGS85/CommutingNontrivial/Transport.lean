module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.Neighborhood

/-!
# Translation of the nontrivial commuting critical branch

The original graph action transports the critical pair, its commuting centers
and the exact nonzero displacement [V_beta intersect Q_alpha', V_alpha']
simultaneously. This supplies conjugation transport without assuming that
reversing a critical pair preserves escape; that is the separate 8.2 argument.

Source: DGS, *Groups and Graphs* (1985), 8.0 and the conjugation convention
following 8.1, pp.132--134.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G) [∀ i, Finite (F i)]

theorem criticalPair_translate {a a' : Vertex F} (hc : IsCriticalPair F a a') (g : G) :
    IsCriticalPair F (g • a) (g • a') := by
  refine ⟨(dist_smul F g a a').trans hc.1, ?_⟩
  intro h
  apply hc.2
  have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h
  rwa [← Z_translate, ← U_translate, inv_smul_smul, inv_smul_smul] at hm

theorem commuting_centers_translate (a a' : Vertex F) (g : G) :
    ⁅Z F (g • a), Z F (g • a')⁆ = (⁅Z F a, Z F a'⁆).map (MulAut.conj g).toMonoidHom := by
  rw [Z_translate, Z_translate, map_commutator]

theorem displacement_translate (beta a' : Vertex F) (g : G) :
    ⁅V F (g • beta) 1 ⊓ Q F (g • a'), V F (g • a') 1⁆ =
      (⁅V F beta 1 ⊓ Q F a', V F a' 1⁆).map (MulAut.conj g).toMonoidHom := by
  rw [V_translate, Q_translate, V_translate, map_commutator,
    map_inf _ _ _ (MulAut.conj g).injective]

/-- Reorienting by any original group element transports the exact critical
pair, commuting centers and nonzero displacement simultaneously. No center
or core-intersection span is substituted for the source radius-one span. -/
theorem branch_translate {a beta a' : Vertex F}
    (hc : IsCriticalPair F a a') (hcomm : ⁅Z F a, Z F a'⁆ = ⊥)
    (hne : ⁅V F beta 1 ⊓ Q F a', V F a' 1⁆ ≠ ⊥) (g : G) :
    IsCriticalPair F (g • a) (g • a') ∧
      ⁅Z F (g • a), Z F (g • a')⁆ = ⊥ ∧
      ⁅V F (g • beta) 1 ⊓ Q F (g • a'), V F (g • a') 1⁆ ≠ ⊥ := by
  refine ⟨criticalPair_translate F hc g, ?_, ?_⟩
  · rw [commuting_centers_translate, hcomm, Subgroup.map_bot]
  · rw [displacement_translate]
    exact fun he => hne ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp he)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
