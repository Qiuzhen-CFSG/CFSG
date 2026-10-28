module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Preliminaries
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.SectionCentralization
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.ChiefFactors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.Construction
public import CFSG.Quasithin.ChapterB.Section02.Thompson

/-!
# Local control in the residual-normalizer argument

The relative residual identities and actual Sylow placement from Preparation
combine with centralization on the original L/O₂(L). Uniqueness over LT and
the escape K ≰ N_G(L) force D₁ = 1, whence D ∩ N_G(L) ≤ T. Independently,
D ∩ T ≤ R₁ and R₁ is an actual Sylow two-subgroup of DR₁.

The original action kernel constructs the genuine central commutator duality.
ChiefFactors then builds a complete L₁-chief series with at least four
noncentral two-factors, from the original natural module and its dual section.
This excludes the first alternative of the universal earlier 14.7.10 and
gives N_G(Baum(R₁)) ≤ N_G(L).

The universal structural and uniqueness inputs are the genuine 12.2.2 and
1.2.7 implications, with producers qt-12-02 and qt-1-02-adequate-assembly.
The source parent qt-14-07-critical-residual-normalizer retains their discharge,
the original compatible UpperMarking from the 14.7.63–65 setup (qt-14-07),
and the two universal earlier implications stated below: 14.5.21(2) from
qt-14-05-terminal-duality and 14.7.10 from qt-14-07-solvable. Neither a chief
count nor a local-control conclusion is assumed for this datum. This completes
the local-control paragraph from those earlier source inputs, not the remaining
Thompson-factorization argument or all of 14.7.67(4).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.67(4), printed p.1070, PDF p.1087.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ResidualNormalizer
universe u

namespace ResidualNormalizer.LocalControl
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

/-- The universal rank-three case of 14.5.21(2), with H ranging over the
actual local family. Its producer is qt-14-05-terminal-duality. -/
def Earlier14521Two : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G)
    (F : InvariantFlag T V 3),
    Counterexample T L → HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3 →
    IsMulCommutative F.U →
    ∀ H ∈ F.Hz L (normalizer (L : Set G)),
      ⁅conjugateSpanBy V H, H.pCoreIn 2⁆ = F.Vi 1

/-- The universal earlier 14.7.10 alternative on the genuine natural L₃(2)
setup. The first alternative bounds every complete chief series of the
literal L₁. Its producer is qt-14-07-solvable. -/
def Earlier14710 : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G)
    (F : InvariantFlag T V 3),
    Counterexample T L → HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3 →
    IsMulCommutative F.U →
      (∀ s : NoncentralChiefRefinement.ChiefSeries (F.Li L 1),
        s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ 3) ∨
      normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G)

end ResidualNormalizer.LocalControl

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The compatibility API with section-centralization supplied explicitly.
The application below discharges this premise on the original datum. -/
theorem Data.residual_local_control_of_sectionCentralization (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (hc : ⁅D₁ L F, L⁆ ≤ L.pCoreIn 2) :
    D₁ L F = ⊥ ∧ D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G) ∧
      D F ⊓ (T : Subgroup G) ≤ F.Ri L 1 ∧
      Chapter1.IsSylowIn 2 (F.Ri L 1) (D F ⊔ F.Ri L 1) := by
  obtain ⟨hz, hi⟩ := d.residual_intersections_of_sectionCentralization structural uniqueness hc
  exact ⟨hz, hi, d.D_inf_T_le_Ri, d.Ri_isSylowIn_D_sup_Ri⟩

/-- Residual vanishing, both intersection bounds, and actual Sylow placement.
The section-centralization premise has been discharged. -/
theorem Data.residual_intersections (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u}) :
    D₁ L F = ⊥ ∧ D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G) ∧
      D F ⊓ (T : Subgroup G) ≤ F.Ri L 1 ∧
      Chapter1.IsSylowIn 2 (F.Ri L 1) (D F ⊔ F.Ri L 1) :=
  d.residual_local_control_of_sectionCentralization structural uniqueness
    (d.D₁_commutator_le_core structural)

/-- Construct the actual duality before counting factors in a complete
chief series of the literal L₁. Only the earlier point commutator remains. -/
theorem Data.exists_residual_four_chief_factors (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (mark : Rechoice.LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ s : NoncentralChiefRefinement.ChiefSeries (F.Li L 1),
      s.head = ⊥ ∧ s.last = ⊤ ∧ 4 ≤ s.noncentralTwoCount := by
  obtain ⟨X, aX, mX, hs⟩ := CriticalIntersections.exists_sourceDuality d
    (d.sectionCentralizer_of_earlier_setup structural uniqueness)
  let := aX
  let := mX
  obtain ⟨s⟩ := hs
  exact ChiefFactors.exists_four_chief_factors_of_earlier_setup d s
    structural uniqueness mark hcomm

/-- The four constructed factors exclude the first alternative of 14.7.10;
the conclusion concerns the Baumann subgroup of the original R₁. -/
theorem Data.baumann_normalizer_le_of_point_commutator (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (earlier : LocalControl.Earlier14710.{u})
    (mark : Rechoice.LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨s, hs0, hs1, hs⟩ :=
    d.exists_residual_four_chief_factors structural uniqueness mark hcomm
  rcases earlier G T L V F d.counterexample d.natural d.abelian with h | h
  · have hle := h s hs0 hs1
    omega
  · exact h

/-- The complete local-control paragraph, allowing the earlier point
commutator to be supplied directly by its source owner. -/
theorem Data.residual_local_control_of_point_commutator (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (earlier : LocalControl.Earlier14710.{u})
    (mark : Rechoice.LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    D₁ L F = ⊥ ∧ D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G) ∧
      D F ⊓ (T : Subgroup G) ≤ F.Ri L 1 ∧
      Chapter1.IsSylowIn 2 (F.Ri L 1) (D F ⊔ F.Ri L 1) ∧
      normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hz, hM, hT, hS⟩ := d.residual_intersections structural uniqueness
  exact ⟨hz, hM, hT, hS,
    d.baumann_normalizer_le_of_point_commutator structural uniqueness earlier mark hcomm⟩

/-- Apply both earlier universal source implications to the original Data.
Membership of H in the local family follows from the earlier singleton
identity; no local intersection, Sylow, or Baumann bound is an input. -/
theorem Data.residual_local_control (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (pointCommutator : LocalControl.Earlier14521Two.{u})
    (baumannAlternative : LocalControl.Earlier14710.{u})
    (mark : Rechoice.LocalGeometry.Preparation.UpperMarking d) :
    D₁ L F = ⊥ ∧ D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G) ∧
      D F ⊓ (T : Subgroup G) ≤ F.Ri L 1 ∧
      Chapter1.IsSylowIn 2 (F.Ri L 1) (D F ⊔ F.Ri L 1) ∧
      normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  have hH : F.H ∈ F.Hz L (normalizer (L : Set G)) := by
    rw [d.unique_Hz]
    exact Set.mem_singleton F.H
  have hcomm := pointCommutator G T L V F d.counterexample d.natural d.abelian F.H hH
  exact d.residual_local_control_of_point_commutator structural uniqueness
    baumannAlternative mark hcomm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
