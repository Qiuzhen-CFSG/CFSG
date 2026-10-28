module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Geometry.FullSeed
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Geometry.LineParabolics
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Geometry.OriginalAmalgam
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.FirstFlagCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalPlane
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.SecondFlag
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.FullSeed

/-!
# The original plane-normalizer application in the solvable amalgam: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/Geometry/OriginalPlane` proof for the local step.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem original_R1_amalgam_conditions_of_plane_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore_at h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore_at h structural D m))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hgenerate : (firstCentralizerResidual L z.val ⊔ (T : Subgroup G)) ⊔
      ((L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) =
        L ⊔ (T : Subgroup G))
    (hsupp : normalizer (L : Set G) =
      L ⊔ (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G))) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
    let P := I ⊔ (T : Subgroup G)
    let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
    let L₂ := (pResidual 2 B).map B.subtype
    let H₀ := P ⊔ B
    let K₁ := (pResidual 2 P).map P.subtype
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let C₁ := H₀ ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
    let C₂ := H₀ ⊓ centralizer ((Z ⊓ centralizer (L₂ : Set G) : Subgroup G) : Set G)
    P ∈ Chapter1.HOver G (T : Set G) ∧ B ∈ Chapter1.HOver G (T : Set G) ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
      B = L₂ ⊔ (T : Subgroup G) ∧
      IsCoatom (B.subgroupOf (L ⊔ (T : Subgroup G))) ∧
      (∀ s : NoncentralChiefRefinement.ChiefSeries L₂,
        s.head = ⊥ → s.last = ⊤ → 3 ≤ s.noncentralTwoCount) ∧
      (Z ⊓ centralizer (P : Set G)).relIndex Z = 2 ∧
      (Z ⊓ centralizer (B : Set G)).relIndex Z = 2 ∧ P ≠ B ∧
      normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
      ¬ ⁅K₁,L₂⁆ ≤ K₁.pCoreIn 2 ∧
      (H₀ ∈ Chapter1.H G →
        H₀ ⊓ normalizer (L : Set G) = B ∧ H₀ ⊓ H = P ∧
        C₁ = P ∧ C₂ = B ∧ (K₁.subgroupOf C₁).Normal ∧ (L₂.subgroupOf C₂).Normal ∧
        (primeToResidual 3 C₁).map C₁.subtype = K₁) := by
  obtain ⟨⟨eL⟩,_,hP,hstar⟩ := original_R1_line_parabolics_at h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  let L₂ := (pResidual 2 B).map B.subtype
  obtain ⟨hquot,hL₂,_,hchief⟩ := original_second_flag_chief_factors D m eL W hW hT
  have hmax := original_second_flag_coatom D m W hW hT
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hT
  have hVB : V ≤ B.pCoreIn 2 := by
    let := D.elementary
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
      (D.le_sylow.trans hTB)
      ((inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
        (normalizer_component_le_module_at h structural D m))
  have hlocalB : B ∈ Chapter1.H G := by
    change B.pCoreIn 2 ≠ ⊥
    intro he
    have hv : V = ⊥ := bot_unique (he ▸ hVB)
    have hc := m.card_module
    rw [hv,card_bot] at hc
    omega
  have hB : B = L₂ ⊔ (T : Subgroup G) := le_antisymm
    (le_embedded_pResidual_sup_sylow_of_normalizes T B (hTB.trans B.le_normalizer))
    (sup_le (map_subtype_le _) hTB)
  have hmax₂ : IsCoatom ((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))) :=
    hB ▸ hmax
  have hres₂ : (pResidual 2 (L₂ ⊔ (T : Subgroup G) : Subgroup G)).map
      (L₂ ⊔ (T : Subgroup G)).subtype = L₂ := by rw [←hB]
  have hgen : (firstCentralizerResidual L z.val ⊔ (T : Subgroup G)) ⊔
      (L₂ ⊔ (T : Subgroup G)) = L ⊔ (T : Subgroup G) := by rw [←hB]; exact hgenerate
  obtain ⟨hseed,_,_,_,hidxP⟩ := original_R1_full_seed_at
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  have hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V := hseed.le.trans inf_le_left
  have hfixed := original_second_flag_fixed D m W hW hT
  have hfixed₂ : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L₂ : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) := by
    rw [←inf_eq_left.mpr hZV,inf_assoc,hfixed,←inf_assoc,inf_eq_left.mpr hZV]
  obtain ⟨_,_,_,_,_,hidxB,hne⟩ := original_R1_amalgam_fixed_data_at
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342 L₂ hfixed₂
  have hrest := original_solvable_amalgam_inputs_at h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342 L₂ hL₂ hmax₂ hres₂ hgen hfixed₂ hsupp
  dsimp only at hidxB hne hrest ⊢
  rw [←hB] at hidxB hne hrest
  exact ⟨hstar.1.1,⟨hlocalB,hTB⟩,hP,hquot,hB,hmax,hchief,hidxP,hidxB,hne,hrest⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
