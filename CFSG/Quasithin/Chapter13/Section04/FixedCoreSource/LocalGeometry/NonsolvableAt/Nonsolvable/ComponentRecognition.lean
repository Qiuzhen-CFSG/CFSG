module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentLinearGeometryAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentRecognitionAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSixGeometryAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.ComponentSeedSource
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.ComponentSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentRecognition
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearGeometry
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentNaturalResidual
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentCoveredFive
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Selecting and marking every escaping component: structure at the original group

At a selected component of C_G(z), the actual 13.3.2 list is reduced using
13.3.16 and the proved A₅ exclusion. Nonzero fixed space also excludes the
covered A₆ row. The remaining covered row is retained as an actual natural
module on the whole moved omega-orbit, with its central-core quotient and
conjugation formula. Its minimality follows from the small-quotient theorem.

All three resulting module types give Ω₁Z(T) = V ∩ Ω₁Z(T) of order four.
The final theorem constructs the component and this marking at any escaping
point from nonsolvability of that point's centralizer. In particular, it does
not assume recognition or transfer nonsolvability between different points.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/ComponentRecognition` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Section08.TransvectionRecognition.Component.ModelExtension
open ChapterB.QuasisimpleSource Chapter1.Section02.LocalModels
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- Every selected component supplies the actual moved-module marking and
full central four-group, including the remaining covered natural branch. -/
theorem selected_component_marking_and_seed_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hKN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U,
      Nonempty (ComponentModuleAt DK z.val) ∧
      U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
      omegaOneCenterAmbient (T : Subgroup G) = V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  rcases selected_component_recognition_at hl h₀ h structural D m h1332 fixed five covered
      h13316 hindex z hzT hzL hK hKN hKM hfK with hlin | hsix | hc
  · obtain ⟨eK⟩ := hlin
    obtain ⟨DK,mark,_,_,_,_,_,hU,_,hZ,hcard,_⟩ := linear_component_geometry_at
      hl h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK.1 hKN hKM hfK eK
    exact ⟨DK,mark,hU,hZ,hcard⟩
  · obtain ⟨eK⟩ := hsix
    obtain ⟨DK,mark,hU,_,_,_,hZ,hcard,_⟩ := ordinary_six_component_geometry_at
      h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hKN hKM hfK eK
    exact ⟨DK,mark,hU,hZ,hcard⟩
  · obtain ⟨_,DK,_,hU,q,e,he⟩ := hc
    let mark : ComponentModuleAt DK z.val := .naturalSix q e he
    have hz1 : z ≠ 1 := fun he => hzL (congrArg Subtype.val he ▸ one_mem _)
    exact ⟨DK,⟨mark⟩,hU,full_seed_of_component_moved_module_at
      h₀ h structural m z hz1 hzT hindex hK.1 hKM DK mark⟩

/-- Apply selection and the module analysis at an arbitrary escaping point.
Nonsolvability belongs to this point; no conclusion about other points is inferred. -/
theorem exists_escaping_component_marking_and_seed_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1338 : ∀ H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G),
      ∀ Y : Subgroup G, Y ≤ H → H ≤ normalizer (Y : Set G) →
        IsPPerfect 2 Y → Y ≤ normalizer (L : Set G) → IsPiGroup twoThreePrimes Y)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hnonsolv : ¬ Group.IsSolvable (centralizer ({z.val} : Set G))) :
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)) ∧
      K ∈ MainForward.faithfulLocalComponents T ∧
      K ∈ Chapter1.LStar G T ∧
      centralizer ({z.val} : Set G) ≤ normalizer (K : Set G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ¬ K ≤ normalizer (L : Set G) ∧
      ¬ L ≤ normalizer (K : Set G) ∧
      let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      ∃ DK : ChosenModule T K U,
        Nonempty (ComponentModuleAt DK z.val) ∧
        U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
          (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
        omegaOneCenterAmbient (T : Subgroup G) = V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
        Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨K,hK,hfK,hstar,hKN,hTK,hKM,hLN⟩ :=
    exists_escaping_component_at h₀ h structural m h1332 h1338 hzT hz1 hzout hnonsolv
  exact ⟨K,hK,hfK,hstar,hKN,hTK,hKM,hLN,
    selected_component_marking_and_seed_at hl h₀ h structural modules D m h1332 fixed
      five covered h13316 hindex z hzT hzL hK hKN hKM hfK⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
