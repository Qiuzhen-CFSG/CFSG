module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsResiduals
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentPreparation
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductCubic
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductLocalFactorsStabilizer

/-!
# TerminalProductLocalFactorsResiduals at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductLocalFactorsResiduals`, with structural
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

theorem Le_eq_pointNormalizer_primeToResidual_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (C : P.ComponentAnalysis) :
    P.Le = (primeToResidual 3 P.pointNormalizer).map P.pointNormalizer.subtype := by
  have h := embedded_primeToResidual_intersection 3
    (normalizer (L : Set G)) P.pointNormalizer
  rw [P.normalizer_residual C,
    inf_eq_right.mpr (P.pointNormalizer_le_original_at structural)] at h
  have he : L ⊓ P.pointNormalizer = L ⊓ P.pointCentralizer := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans S.chosen.normalizes) inf_le_right)
  rw [he] at h
  exact P.Le_eq_point_primeToResidual.trans h

theorem Le_eq_pointResidual_sup_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.Le = P.firstPointResidual ⊔ P.secondPointResidual := by
  let M := P.pointNormalizer
  let A := P.firstPointFactor.subgroupOf M
  let B := P.secondPointFactor.subgroupOf M
  have hAM : P.firstPointFactor ≤ M := map_subtype_le _
  have hBM : P.secondPointFactor ≤ M := map_subtype_le _
  let : A.Normal := normal_subgroupOf_of_le_normalizer P.firstPointFactor_normalized
  let : B.Normal := normal_subgroupOf_of_le_normalizer P.secondPointFactor_normalized
  have hgen : A ⊔ B = ⊤ := by
    rw [←subgroupOf_sup hAM hBM,←P.pointNormalizer_eq_factor_sup_at structural escape]
    exact subgroupOf_self _
  have h := congrArg (map M.subtype)
    (primeToResidual_eq_sup_of_normal_generators 3 A B hgen)
  rw [Subgroup.map_sup,map_embedded_primeToResidual_of_hom,
    map_embedded_primeToResidual_of_hom,
    map_subgroupOf_eq_of_le hAM,map_subgroupOf_eq_of_le hBM] at h
  exact (P.Le_eq_pointNormalizer_primeToResidual_at structural C).trans h

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

