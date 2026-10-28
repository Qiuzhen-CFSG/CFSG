module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneNonsolvableSourceAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OriginalComponentPairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SeedGeometryAt

/-!
# Guarded linear selection at every original escaping point

Construct the actual original plane and outside S3 parabolic in both surviving
escaping-component rows. Their chief bound, fixed indices and relative
centralizers supply the literal amalgam hypotheses. When the resulting join
is nonsolvable, guarded model selection excludes A6 and gives an actual
linear-three component with full movement of the second two-residual by J1(T).
The full linear overgroup formula is also supplied on this same join.

The solvable join alternative is retained as a conclusion; no premise asserts
its exclusion or assumes nonsolvability at a different escaping point.
All earlier module/catalogue/unitary and large-distance inputs remain explicit.
The solvable plane branch and ambient recognition still need their assembly.
Source: Aschbacher--Smith 13.4.7(4) and 13.4.10(8), pp.902--903,909--910.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- On the actual plane pair at every nonsolvable escaping point, either
the join is solvable or the complete linear conclusion and residual movement
hold. Both original escaping-component rows are covered. -/
theorem original_escaping_plane_linear_alternative_at
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
        let L₂ := (pResidual 2 B).map B.subtype
        Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
        X ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G) ∧
        Z = V ⊓ Z ∧ Nat.card Z = 4 ∧
        (Group.IsSolvable X ∨
          ⁅L₂,ChapterB.thompsonJ (T : Subgroup G) 1⁆ = L₂ ∧
          Solvable.LinearAmalgamConclusion T X ∧
          ¬ X ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G)) := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨m,W,hW,hT,P,hP,hPH,⟨eP⟩,⟨eB⟩,_,hlocal,_,hchief,hiP,hiB,_,hcentral⟩ :=
    original_escaping_component_pair_at hl h₀ D hfixed structural modules earlier h1332
      fixed five covered h13316 z hzT hzL hout hnonsolv
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hT
  have hBM : B ≤ normalizer (L : Set G) :=
    inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hne : P ≠ B := fun he => hP.1.2 (he ▸ hBM)
  have hindex := original_omega_fixed_index_at h₀ h structural D m earlier
  have hcentral' : let X := P ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let R := (pResidual 2 P).map P.subtype
      let S := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (R : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (S : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (R.subgroupOf C₁).Normal ∧ (S.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = R ∨
          (primeToResidual 3 C₂).map C₂.subtype = S) := by
    dsimp only
    intro hx
    obtain ⟨_,_,_,_,h₁,h₂,hr⟩ := hcentral (P ⊔ B) hx.1 le_sup_left le_sup_right
    exact ⟨h₁,h₂,Or.inl hr⟩
  have hseed := Amalgam.original_pair_source_seed_at h structural D m hP.1.1.2 hTB
    eP eB hne hindex hiP hiB hcentral'
  refine ⟨m,W,hW,hT,P,hP,hPH,⟨eP⟩,⟨eB⟩,hseed.1,hseed.2.1,hseed.2.2.1,?_⟩
  by_cases hs : Group.IsSolvable (P ⊔ B : Subgroup G)
  · exact Or.inl hs
  · exact Or.inr (Amalgam.original_plane_nonsolvable_source_at h₀ D m h1332 fixed covered
      hP.1.1.2 hTB eP eB hne hiP hiB hcentral' h13316
      h structural hindex hs hl W hW hT rfl).2

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
