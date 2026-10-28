module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneSourceAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OriginalComponentPairAt

/-!
# The guarded plane theorem on the original escaping-point pair

At every nonsolvable escaping point, the two surviving component rows supply
the actual marked plane and outside S3 parabolic. Their source chief bound,
fixed indices and relative-centralizer identities discharge the restricted
plane theorem. The component geometry also proves N_G(L)=LT on this same
original module. The conclusion is the source residual two-core containment
or the full linear amalgam conclusion; solvability is no longer an unresolved
alternative. The literal identity K2=L2 is proved using the same normalizer.

Both original component rows and all earlier-source premises are retained.
This does not assert nonsolvability at another escaping point or complete
ambient symplectic recognition.
Source: Aschbacher--Smith 13.4.7 and 13.4.10(8), pp.899--904,909--910.
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

/-- Discharge the restricted plane premises for the actual pair at every original
nonsolvable escaping point, in both the linear-three and ordinary A6 rows. -/
theorem original_escaping_plane_source_at
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
        X ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G) ∧
        Z = V ⊓ Z ∧ Nat.card Z = 4 ∧
        (⁅K₂,L₂⁆ ≤ K₂.pCoreIn 2 ∨ Solvable.LinearAmalgamConclusion T X) := by
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
  have hB : B ∈ Chapter1.HOver G (T : Set G) := by
    have hVB : V ≤ B.pCoreIn 2 := by
      let := D.elementary
      exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
        (D.le_sylow.trans hTB) (hBM.trans (normalizer_component_le_module_at h structural D m))
    refine ⟨?_,hTB⟩
    intro he
    exact D.ne_bot (bot_unique (he ▸ hVB))
  have hindex := original_omega_fixed_index_at h₀ h structural D m earlier
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨K,hK,hfK,_,hKN,_,hKM,_⟩ :=
    augmentation_exists_escaping_component_at h₀ h structural m h1332 hzT hz1 hout hnonsolv
  have hrows := selected_component_rows_at hl h₀ h structural D m h1332 fixed five covered
    h13316 hindex z hzT hzL hK hKN hKM hfK
  have hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G) := by
    rcases hrows with h3 | h6
    · exact (linear_component_normalizer_supplement_at hl h₀ h structural modules D m
        h1332 fixed hindex z hzT hzL hK.1 hKN hKM hfK h3.some).2.2.1
    · exact (six_component_normalizer_supplement_at h₀ h structural modules D m
        h1332 fixed hindex z hzT hzL hK hKN hKM hfK h6.some).2.2.1
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
  have hres : (pResidual 2 B).map B.subtype =
      (pResidual 2 (L ⊓ normalizer (m.naturalPreimage W : Set G) : Subgroup G)).map
        (L ⊓ normalizer (m.naturalPreimage W : Set G)).subtype := by
    rw [show B = (L ⊓ normalizer (m.naturalPreimage W : Set G)) ⊔ (T : Subgroup G) from
      Solvable.second_flag_normalizer_eq D _ hT]
    exact Solvable.second_parabolic_full_residual _
      (m.sylow_normalizes_inner_plane W hT)
  have hpair := Amalgam.planeAmalgamSource1347_at hl h₀ h structural modules D m h1332
    fixed covered h13316 hindex hM W hW hT P hP.1.1 hB ⟨eP⟩ ⟨eB⟩ hne hres
    (Or.inr (fun s hs ht => le_trans (by decide : 2 ≤ 3) (hchief s hs ht)))
    hiP hiB hcentral'

  exact ⟨m,W,hW,hT,P,hP,hPH,⟨eP⟩,⟨eB⟩,hseed.1,hseed.2.1,hseed.2.2.1,hpair.2⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
