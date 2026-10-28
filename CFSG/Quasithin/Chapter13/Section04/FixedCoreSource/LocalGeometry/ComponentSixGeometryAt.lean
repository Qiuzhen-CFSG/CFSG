module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentNonsplitAt

/-!
# Original selected ordinary-six geometry from guarded inputs

Assemble the fixed-free natural and nonsplit augmentation cases on the
same moved omega orbit. Both supply the chosen module, whole-module
marking, original ordinary quotient, L1 containment, full omega center of
order four and the two literal reciprocal residual identities.

The original-module application constructs Hypothesis1223, the augmentation
marking and omega index from the original fixed-module and earlier source
inputs. It also constructs the selected ordinary quotient whenever the
selected moved module has a fixed vector. Thus no fixed-space case split,
index, marking or universal structural premise is added to that application.
This is the selected-six branch of 13.4.10; selecting among all component
rows and final 13.4.1 recognition remain separate obligations.
Source: Aschbacher--Smith 13.4.10(2--5), printed pp.907--909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- Original 13.4.10(2--5) in the ordinary selected A₆ row, with both possible
fixed-space cases assembled on the same literal moved orbit. -/
theorem ordinary_six_component_geometry_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U,
      Nonempty (ComponentModuleAt DK z.val) ∧
      U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Solvable.firstCentralizerResidual L z.val ≤ K ∧
      primeRank 3 (Solvable.firstCentralizerResidual L z.val) = 1 ∧
      omegaOneCenterAmbient (T : Subgroup G) =
        V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 ∧
      Solvable.firstCentralizerResidual K m.constant.val =
        Solvable.firstCentralizerResidual L z.val ∧
      (pResidual 2 (K ⊓ centralizer
          (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Subgroup G)).map
          (K ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype =
        (pResidual 2 (L ⊓ centralizer ({z.val} : Set G) : Subgroup G)).map
          (L ⊓ centralizer ({z.val} : Set G)).subtype := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  by_cases hfixed : U ⊓ centralizer (K : Set G) = ⊥
  · obtain ⟨DK,_,_,_,hUR,mark,hZ,hcard⟩ := ordinary_six_component_marking_at
      h₀ h structural modules D m h1332 hindex z hzT hzL hK.1 hHN hKM hfK eK hfixed
    obtain ⟨hL,hLK,hr,_,_,hrec,hres⟩ := ordinary_original_of_fixedFree_six_component_at
      h₀ h structural modules D m h1332 hindex z hzT hzL hK hHN hKM hfK eK hfixed
    exact ⟨DK,mark,hUR,hL,hLK,hr,hZ,hcard,hrec,hres⟩
  · obtain ⟨DK,_,_,hUR,mark,hZ,hcard⟩ := component_core_marking_of_source_fixed_at
      h₀ h structural m h1332 fixed hindex z.property hzT hz1 hK.1 hHN hKM hfK hfixed
    obtain ⟨hL,hLK,hr,_,hres⟩ := ordinary_original_of_nonsplit_ordinary_component_at
      h₀ h structural m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK hfixed
    obtain ⟨eL⟩ := hL
    have hrec := component_reciprocal_residual_of_ordinary_six_at h₀ h structural m hzT hz1
      hK hHN (component_quotient_quasisimple h1332 hfK) eK eL
    exact ⟨DK,mark,hUR,⟨eL⟩,hLK,hr,hZ,hcard,hrec,hres⟩

/-- Apply the selected-six geometry to the original chosen module. A nonzero
fixed space in the selected moved orbit suffices in place of a supplied ordinary
selected quotient; the covered selected alternative is excluded internally. -/
theorem original_six_component_geometry_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hrow : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) ∨
      (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
        Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    ∃ m : CoreMarking D,
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U,
      Nonempty (ComponentModuleAt DK z.val) ∧
      U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Solvable.firstCentralizerResidual L z.val ≤ K ∧
      primeRank 3 (Solvable.firstCentralizerResidual L z.val) = 1 ∧
      omegaOneCenterAmbient (T : Subgroup G) =
        V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 ∧
      Solvable.firstCentralizerResidual K m.constant.val =
        Solvable.firstCentralizerResidual L z.val ∧
      (pResidual 2 (K ⊓ centralizer
          (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Subgroup G)).map
          (K ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype =
        (pResidual 2 (L ⊓ centralizer ({z.val} : Set G) : Subgroup G)).map
          (L ⊓ centralizer ({z.val} : Set G)).subtype := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  have hindex := original_omega_fixed_index_at h₀ h structural D m earlier
  have heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) := by
    rcases hrow with heK | hfixedK
    · exact heK
    · exact ordinary_component_of_source_fixed_at h₀ h structural D m h1332 fixed
        hindex z hzT hzL hK hHN hKM hfK hfixedK
  obtain ⟨eK⟩ := heK
  exact ⟨m,ordinary_six_component_geometry_at h₀ h structural modules D m h1332
    fixed hindex z hzT hzL hK hHN hKM hfK eK⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
