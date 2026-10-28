module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentAmbientUniqueness
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisFusion
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentAmbientGeneration

/-!
# TerminalComponentAmbientUniqueness at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentAmbientUniqueness`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem weightSixMovement_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) : P.WeightSixMovement := by
  let E : S.NaturalCoordinates :=
    ⟨D.model.coordinates, fun l v => by
      simpa only [D.component_action] using
        D.model.equivariant ⟨l, S.chosen.normalizes l.property⟩ v⟩
  obtain ⟨f, hf, hfc⟩ := E.central_representative_weight_at structural
    (n := 6) (Or.inr (Or.inr rfl))
  have hf1 : f ≠ 1 := by
    intro he
    have hzero : weight (0 : Word) = 0 := by decide
    have hh := hf
    change weight (D.model.coordinates f).toAdd.val = 6 at hh
    simp only [he, map_one] at hh
    exact (by decide : (0 : ℕ) ≠ 6) (hzero.symm.trans hh)
  have hfZ : (f : G) ∈ P.Z := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨S.chosen.le_sylow f.property, hfc, ?_⟩
    let := S.chosen.elementary
    exact elemPow_eq_one_of_isElementaryAbelian _ f.property
  exact ⟨f, hf1, hf, hfZ, P.Le_not_le_weight_six_centralizer f hf⟩

theorem overcomponent_le_normalizer_of_natural_omega_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : P.Overcomponents) {W : Subgroup G} (SY : Setup T F.Y W)
    (DY : SY.NaturalCoordinates) (hsplit : SY.NaturalOmegaDecomposition)
    (hLe : P.Le ≤ F.Y) : F.Y ≤ normalizer (L : Set G) :=
  overcomponent_le_normalizer_of_point_generation_at F SY
    (P.weightSixMovement_at structural)
    (SY.centralVectorMaximality_of_coordinates_omega DY hsplit) hLe

theorem ambientA5Uniqueness_of_natural_omega_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : P.Overcomponents) {W : Subgroup G} (SY : Setup T F.Y W)
    (DY : SY.NaturalCoordinates) (hsplit : SY.NaturalOmegaDecomposition) :
    AmbientA5Uniqueness (P := P) F := by
  intro W' _ _ hLe
  have hYM := P.overcomponent_le_normalizer_of_natural_omega_at
    structural F SY DY hsplit hLe
  exact False.elim (P.residual_escape_at structural
    (F.residual_le.trans (F.le_maximal.trans hYM)))

theorem proper_component_eq_residual_of_natural_omega_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (R : P.ResidualAnalysis) (F : P.Overcomponents)
    (hKY : P.K < F.Y) {W : Subgroup G} (SY : Setup T F.Y W)
    (DY : SY.NaturalCoordinates) (hsplit : SY.NaturalOmegaDecomposition)
    (A : A314RestrictionInput (P := P))
    (hLe : F.E = F.Y → P.Le ≤ F.Y) : F.E = P.K :=
  proper_component_eq_residual_at structural R F hKY SY A hLe
    (P.ambientA5Uniqueness_of_natural_omega_at structural F SY DY hsplit)

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

