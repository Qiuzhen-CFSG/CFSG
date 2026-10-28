module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.ClassificationInput
public import CFSG.Quasithin.ChapterC.Section01.NaturalPointControl.ClassificationExclusions

/-!
# The surviving C.1.34 cases in the original Baumann countercase

Apply the binary classification to the actual MS pair in L Baum(R₁).
The point exclusion proves that its commutator core is a natural module or
a double natural module. The OriginalClassification consumer retains the literal Rudvalis datum and
its complete chief series of F.Li L 1 with four noncentral two-factors.

The classifier remains the independent source premise owned by
qt-rank-two-ms93. Task qt-d-14710-baumann retains the chief-factor upper
bound and its comparison with these four factors; final 14.7.75 assembly
is owned by qt-d-14775-source. This result is not Earlier14710.

Source: Aschbacher--Smith C.1.37, printed p.143; 14.7.10, p.1045;
and the original 14.7.67(4) application, p.1070.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.LocalControl.OriginalSource
open Subgroup ChapterC.NaturalPointControl
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u

/-- Precisely the binary specialization of the independent C.1.34 theorem. -/
def BinaryMSClassification (κ : GroupClass.{u}) : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (K R : Subgroup J),
    SmallMSPair κ K R →
    Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ S : Subgroup J, Chapter1.IsSylowIn 2 S (K ⊔ R) → R ≤ S →
      ∃ e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        MSModuleAlternatives K R S 1 (ZMod 2) e

variable {X : Type u} [Group X] [Finite X] {V : Subgroup X} [V.Normal]
  [IsElementaryAbelian 2 V] {κ : GroupClass.{u}}

/-- The five-way classifier leaves only the two small commutator-core models
on the original natural-point MS pair, with one marking in each conclusion. -/
theorem natural_or_double_of_classification (binary : BinaryMSClassification κ)
    (a : NaturalAction V) (h : ChapterC.BinaryMS.Input κ a.LJ a.BJ) :
    ∃ e : (a.LJ ⧸ pCore 2 a.LJ) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      HasSectionModel a.LJ (msQ a.LJ a.BJ) ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := ZMod 2) 3) ∨
      HasSectionModel a.LJ (msQ a.LJ a.BJ) ⊥ (linearThreeActor e)
        ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
          (Representation.specialLinearNatural (k := ZMod 2) 3)) := by
  obtain ⟨S,hS⟩ := h.radical.isPGroup.exists_le_sylow
  have hs : Chapter1.IsSylowIn 2 (S : Subgroup a.J) (a.LJ ⊔ a.BJ) := by
    rw [h.sup_eq_top]
    exact Chapter1.isSylowIn_iff.mpr ⟨S.isPGroup',le_top,fun U hu hsu _ => S.is_maximal' hu hsu⟩
  obtain ⟨e,he⟩ := binary a.J a.LJ a.BJ (smallMSPair_of_input h) ⟨h.quotientEquiv⟩ S hs hS
  exact ⟨e,a.ms_natural_or_double h S hS e he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.LocalControl.OriginalSource

