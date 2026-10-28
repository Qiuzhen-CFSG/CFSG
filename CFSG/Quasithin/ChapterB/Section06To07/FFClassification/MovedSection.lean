module

public import Theory.Representation.BinaryOffender.NonStrongMovedSection
public import Theory.Representation.BinaryOffender.PerfectCentralizer
public import Theory.Representation.SL2NaturalOffenders.NoStrong
public import Theory.Representation.BinaryOffender.Replacement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions

/-!
# Source factor sections retain the whole normalizer action

The ratio-one source row rules out a strong image of the selected minimal
best offender. The original Irr+ section is consequently exactly [V,L],
and its quotient by C_W(L) carries the action of N_G(L), extending its
original L-action. The second application discharges the non-strong bound
from a literal faithful natural SL2 quotient of the actual action image;
no splitting or equality W=[V,L] is assumed.

Source: Aschbacher–Smith, proof of B.6.9(a), printed p.116, using B.1.5
and the natural SL2 row of B.4.2 (1 March 2004 manuscript). Passage from
the normalizer to its centralizer quotient remains a separate step.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The earlier ratio-one row constructs the actual moved section and its normalizer extension. -/
theorem moved_section_of_ratio_one
    {L A : Subgroup G} {W : Submodule (ZMod 2) V}
    (hA : IsMinimalBestOffender ρ A) (hW : IsIrrPlus ρ L W)
    (hAW : A ≤ subspaceStabilizer ρ W) (hgen : ⁅L,A⁆ = L)
    (hq : quadraticRatio (subspaceImageRepresentation ρ W) = 1) :
    W = subspaceCommutator ρ ⊤ L ∧
      ∃ hN : normalizer (L : Set G) ≤ subspaceStabilizer ρ W,
        (centralSectionRepresentation ρ L (normalizer (L : Set G)) W hN le_rfl).comp
          (inclusion L.le_normalizer) = centralQuotientRepresentation ρ L W hW.choose := by
  have hn : ¬ IsStrongFFModule (subspaceImageRepresentation ρ W) := by
    rw [isStrongFFModule_iff_quadraticRatio_lt_one, hq]
    exact lt_irrefl _
  have hns : ¬ IsStrongOffender (subspaceImageRepresentation ρ W)
      (restrictedSubgroup ρ W A) := fun hs => hn ⟨_,hs⟩
  exact ⟨hA.irrPlus_eq_moved_of_non_strong ρ hW hAW hgen hns,
    hA.irrPlus_normalizer_extension_of_non_strong ρ hW hAW hgen hns⟩

/-- A faithful natural quotient of the actual section image supplies the required source bound. -/
theorem moved_section_of_natural_two_quotient
    {L A : Subgroup G} {W : Submodule (ZMod 2) V}
    (hA : IsMinimalBestOffender ρ A) (hW : IsIrrPlus ρ L W)
    (hAW : A ≤ subspaceStabilizer ρ W) (hgen : ⁅L,A⁆ = L)
    (F : QuasisimpleSource.BinaryField)
    (j : subspaceActionImage ρ W →* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
    (hj : Function.Injective j) (p : W →ₗ[ZMod 2] (Fin 2 → F.Carrier))
    (hp : Function.Surjective p)
    (he : ∀ g w, p (subspaceImageRepresentation ρ W g w) =
      SL2NaturalOffenders.NoStrong.natural (j g) (p w)) :
    W = subspaceCommutator ρ ⊤ L ∧
      ∃ hN : normalizer (L : Set G) ≤ subspaceStabilizer ρ W,
        (centralSectionRepresentation ρ L (normalizer (L : Set G)) W hN le_rfl).comp
          (inclusion L.le_normalizer) = centralQuotientRepresentation ρ L W hW.choose := by
  have hn := SL2NaturalOffenders.NoStrong.not_strong_of_natural_quotient
    (subspaceImageRepresentation ρ W) j hj p hp he
  have hns : ¬ IsStrongOffender (subspaceImageRepresentation ρ W)
      (restrictedSubgroup ρ W A) := fun hs => hn ⟨_,hs⟩
  exact ⟨hA.irrPlus_eq_moved_of_non_strong ρ hW hAW hgen hns,
    hA.irrPlus_normalizer_extension_of_non_strong ρ hW hAW hgen hns⟩

/-- A distinct actual component centralizes the source moved factor. -/
theorem other_component_moved_eq_bot
    {L K A : Subgroup G} {W : Submodule (ZMod 2) V}
    (hL : IsComponent G L) (hK : IsComponent G K) (hne : K ≠ L)
    (hA : IsMinimalBestOffender ρ A) (hW : IsIrrPlus ρ L W)
    (hAW : A ≤ subspaceStabilizer ρ W) (hgen : ⁅L,A⁆ = L)
    (hq : quadraticRatio (subspaceImageRepresentation ρ W) = 1) :
    subspaceCommutator ρ W K = ⊥ := by
  let := hK.2
  obtain ⟨_,hN,_⟩ := moved_section_of_ratio_one ρ hA hW hAW hgen hq
  have hc : K ≤ centralizer (L : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hK.commutator_eq_bot_of_ne hL hne)
  exact (subspaceCommutator_eq_bot_iff ρ W K).mpr
    (hW.le_fixedSpace_of_perfect_centralizes ρ hc
      (hc.trans ((Subgroup.centralizer_le_normalizer _).trans hN)))

end CFSG.Quasithin.ChapterB
