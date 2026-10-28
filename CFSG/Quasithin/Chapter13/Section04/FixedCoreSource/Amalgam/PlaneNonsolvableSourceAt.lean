module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ApplicableNonsolvable
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneModelSelectionAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearSourceConclusionAt

/-!
# The complete guarded nonsolvable branch of the original plane theorem

The actual pair first supplies locality and escape, so clause (c) gives
the original relative residual identity. The original plane marking then
selects an actual linear component and proves full second-residual movement.
The guarded linear theorem supplies its whole overgroup product, along
with the required component family and Thompson normality conclusions.

This discharges every model, movement, shortness and overgroup premise for
the nonsolvable plane branch. The solvable noncommuting exclusion remains
separate. Earlier catalogue/module/unitary and natural large-distance inputs
remain explicit and must be discharged by final source assembly.
Source: Aschbacher--Smith 13.4.7(1ii),(2),(4), printed pp.899--903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
variable
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)

variable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hnonsolv : ¬ Group.IsSolvable (A ⊔ B : Subgroup G))


include h₀ D m h1332 fixed covered hTA hTB eA eB hne hindexA hindexB hcentral h13316
  h structural hindexL hnonsolv

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- The admitted nonsolvable plane pair satisfies the full linear conclusion;
no escape, unconditional relative residual, or model marking is supplied. -/
theorem original_plane_nonsolvable_source_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) :
    A ⊔ B ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G) ∧
      ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
        (pResidual 2 B).map B.subtype ∧
      Solvable.LinearAmalgamConclusion T (A ⊔ B) ∧
      ¬ A ⊔ B ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
  have ho := original_pair_outside h.toHypothesis1221 D m hTA hTB eA eB hne
    hindexL hindexA hindexB hcentral
  obtain ⟨K,hK,⟨eK⟩,hc,hn⟩ := original_pair_nonsolvable_plane_linear_at
    h₀ D m h1332 fixed covered hTA hTB eA eB hne hindexA hindexB
    (hcentral ho.1).2.2 h13316 h structural ho.2 hindexL hnonsolv hl W hW hTW hB
  exact ⟨ho,hc,original_pair_linear_amalgam_conclusion_at h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK (hcentral ho.1).2.2 eK
    h structural ho.2 hindexL hc,hn⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
