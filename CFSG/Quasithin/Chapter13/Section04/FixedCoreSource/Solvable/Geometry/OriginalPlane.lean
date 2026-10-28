module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.SecondFlag
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.FullSeed

/-!
# The original plane-normalizer application in the solvable amalgam

Use B=N_LT(V₂), for the actual T-invariant plane preimage, and
L₂=O²(B). The source local product selects the ordinary A₆ row. The
plane alignment then constructs the S₃ quotient, chief-factor bound and
maximality; the previously proved full omega-center containment restricts
C_V(L₂)=C_V(L) to the exact fixed line required in 13.4.7(b–c).
The original Sylow supplement also identifies B=L₂T. The chosen V lies
in O₂(B), proving B∈H(T); the checked HStar membership places IT in
the same family.

This applies the relative-centralizer and product-exclusion arguments to
H₀=⟨IT,B⟩ without an assumed second-parabolic marking, maximality or
fixed-line equality. The earlier generating pair, normalizer supplement,
13.2–13.3 inputs and genuine universal Structural1222 remain explicit.
Their discharge and the 13.4.7 alternatives belong to
qt-d-1341-fixed-core-source, the replacement owner of the retired
qt-d-1341-local-amalgam-source task. H₀'s L₃(2) quotient, the marked
C₃ system and ambient fusion remain with qt-d-1341-solvable-source.
This result does not assert H₀ is two-local before applying 13.4.7.
Source: Aschbacher–Smith 13.4.9, printed p.906, using 13.4.7(a–c).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem original_R1_amalgam_conditions_of_plane
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m))
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
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
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
  obtain ⟨⟨eL⟩,_,hP,hstar⟩ := original_R1_line_parabolics h₀ h structural D m hcase z hz hzL
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
        (normalizer_component_le_module h structural D m))
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
  obtain ⟨hseed,_,_,_,hidxP⟩ := original_R1_full_seed
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  have hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V := hseed.le.trans inf_le_left
  have hfixed := original_second_flag_fixed D m W hW hT
  have hfixed₂ : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L₂ : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) := by
    rw [←inf_eq_left.mpr hZV,inf_assoc,hfixed,←inf_assoc,inf_eq_left.mpr hZV]
  obtain ⟨_,_,_,_,_,hidxB,hne⟩ := original_R1_amalgam_fixed_data
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342 L₂ hfixed₂
  have hrest := original_solvable_amalgam_inputs h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342 L₂ hL₂ hmax₂ hres₂ hgen hfixed₂ hsupp
  dsimp only at hidxB hne hrest ⊢
  rw [←hB] at hidxB hne hrest
  exact ⟨hstar.1.1,⟨hlocalB,hTB⟩,hP,hquot,hB,hmax,hchief,hidxP,hidxB,hne,hrest⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
