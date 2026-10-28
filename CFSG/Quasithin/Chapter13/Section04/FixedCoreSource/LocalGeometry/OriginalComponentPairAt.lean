module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentLinearPairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSixPairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OriginalComponentGeometryAt

/-!
# The original nonsolvable plane pair from guarded earlier inputs

At every original nonsolvable escaping point, construct the augmentation
marking, Chapter 12 guard and escaping relatively normal component. Apply
the completed linear-three or ordinary A₆ geometry to build the actual
outside parabolic and invariant original plane. Both rows discharge all
applicability clauses of 13.4.7: the local join, chief count, two fixed-line
indices, relative normality and literal prime-to-three residual identity.

Neither a component row nor a plane, parabolic, normalizer supplement or
amalgam conclusion is assumed. The genuine earlier Chapter 12/13.3 clauses
and natural LargeDistanceInput retain their independent producers. Applying
the guarded amalgam theorem and completing ambient recognition remain.
Source: Aschbacher--Smith 13.4.10(8), printed pp.909--910.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

open Section03.Noncentrality.SupercriticalSource
theorem original_escaping_component_pair_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hnonsolv : ¬ Group.IsSolvable (centralizer ({z.val} : Set G))) :
    ∃ m : CoreMarking D,
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      ∃ P : Subgroup G,
        P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        P ⋖ centralizer ({z.val} : Set G) ∧
        Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
        let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
        let X := P ⊔ B
        let Z := omegaOneCenterAmbient (T : Subgroup G)
        let K₂ := (pResidual 2 P).map P.subtype
        let L₂ := (pResidual 2 B).map B.subtype
        Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
        B = L₂ ⊔ (T : Subgroup G) ∧ X ∈ Chapter1.HOver G (T : Set G) ∧
        L₂ ≤ L ∧
        (∀ s : NoncentralChiefRefinement.ChiefSeries L₂,
          s.head = ⊥ → s.last = ⊤ → 3 ≤ s.noncentralTwoCount) ∧
        (Z ⊓ centralizer (P : Set G)).relIndex Z = 2 ∧
        (Z ⊓ centralizer (B : Set G)).relIndex Z = 2 ∧
        Z ⊓ centralizer (L₂ : Set G) = V ⊓ centralizer (L : Set G) ∧
        (∀ Y : Subgroup G, Y ∈ Chapter1.H G → P ≤ Y → B ≤ Y →
          let C₁ := Y ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
          let C₂ := Y ⊓ centralizer ((Z ⊓ centralizer (L₂ : Set G) : Subgroup G) : Set G)
          Y ⊓ normalizer (L : Set G) = B ∧
          Y ⊓ centralizer ({z.val} : Set G) = P ∧
          C₁ = P ∧ C₂ = B ∧ (K₂.subgroupOf C₁).Normal ∧ (L₂.subgroupOf C₂).Normal ∧
          (primeToResidual 3 C₁).map C₁.subtype = K₂) := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  have hindex := original_omega_fixed_index_at h₀ h structural D m earlier
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨K,hK,hfK,hstarK,hKN,hTK,hKM,hLK⟩ :=
    augmentation_exists_escaping_component_at h₀ h structural m h1332 hzT hz1 hout hnonsolv
  have hrows := selected_component_rows_at hl h₀ h structural D m h1332 fixed five covered
    h13316 hindex z hzT hzL hK hKN hKM hfK
  rcases hrows with h3 | h6
  · obtain ⟨eK⟩ := h3
    exact ⟨m,linear_original_pair_at hl h₀ h structural modules D m h1332 fixed hindex
      z hzT hzL hK.1 hKN hKM hfK eK⟩
  · obtain ⟨eK⟩ := h6
    exact ⟨m,ordinary_six_original_pair_at h₀ h structural modules D m h1332 fixed hindex
      z hzT hzL hK hKN hKM hfK eK⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
