module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Geometry.LineParabolics
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Geometry.OriginalPlane
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Geometry.VertexResidues
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.CoveredPlacement
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.CoveredSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.FirstFlagCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Representatives
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalChamber
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.VertexResidues
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Representatives

/-!
# The marked C₃ system and fusion application on the original R₁: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/Geometry/OriginalChamber` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3 Quasithin.I5
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- All three literal vertex residues follow from the source local product,
the original plane, and the third-vertex quotient from 13.4.7. -/
theorem original_R1_three_residues_at
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
      L ⊔ (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)))
    (hthird :
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let X := (I ⊔ (T : Subgroup G)) ⊔ B
      Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)) :
    let M := normalizer (L : Set G)
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
    let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
    let X := (I ⊔ (T : Subgroup G)) ⊔ B
    (Nonempty ((M ⧸ pCore 2 M) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6))) ∧
    Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
    Quasithin.I5.RankTwoParabolics M ((T : Subgroup G).subgroupOf M)
      (H.subgroupOf M) (X.subgroupOf M) ∧
    Quasithin.I5.RankTwoParabolics H ((T : Subgroup G).subgroupOf H)
      (M.subgroupOf H) (X.subgroupOf H) ∧
    Quasithin.I5.RankTwoParabolics X ((T : Subgroup G).subgroupOf X)
      (M.subgroupOf X) (H.subgroupOf X) ∧
    M ⊓ H ⊓ X = (T : Subgroup G) := by
  let M := normalizer (L : Set G)
  let H := centralizer ({z.val} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
  let P := I ⊔ (T : Subgroup G)
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  let X := P ⊔ B
  obtain ⟨_,_,⟨eP⟩,⟨eB⟩,_,hmax,_,_,_,_,hM,_,hrest⟩ :=
    original_R1_amalgam_conditions_of_plane_at h₀ h structural D m hcase z hz hzL hVJ hout
      hfusion h1339 hsolv hindex h1342 W hW hT hgenerate hsupp
  obtain ⟨⟨eL⟩,hl,_,_⟩ := original_R1_line_parabolics_at h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342
  obtain ⟨_,hH,_,_,_,hinter,_,_,_⟩ := centralizer_pair_quotient_of_original_R1_at
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  obtain ⟨eX⟩ := hthird
  have hTX : (T : Subgroup G) ≤ X := le_sup_of_le_left le_sup_right
  have hlocal := third_vertex_local_of_linear_quotient D m X hTX eX
  obtain ⟨hXM,hXH,_⟩ := hrest hlocal
  change X ⊓ M = B at hXM
  change X ⊓ H = P at hXH
  have hBM : B ≤ M := inf_le_left.trans
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hT
  have hmaxM : IsCoatom (B.subgroupOf M) := by rw [show M = L ⊔ (T : Subgroup G) from hM]; exact hmax
  have hgenM : (H ⊓ M) ⊔ B = M := by
    rw [show H ⊓ M = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) from hinter]
    exact hgenerate.trans hM.symm
  have hp := original_point_parabolics_at h structural D m eL hM z hz hzL hinter
    B hBM hTB eB hmaxM hgenM
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans
      ((firstFlagCore_local_data_at h structural D m z hz hzL).1.trans hTH))
  obtain ⟨hi,hplane⟩ := third_vertex_parabolics M H P B X D.sylow_normalizes_component
    le_sup_right hTB (sup_le hIH hTH) hBM le_sup_left le_sup_right eP eB eX hl
  have hXM₁ : X.subgroupOf M = B.subgroupOf M := by
    simpa only [inf_subgroupOf_right] using congrArg (fun A : Subgroup G => A.subgroupOf M) hXM
  have hXH₁ : X.subgroupOf H = P.subgroupOf H := by
    simpa only [inf_subgroupOf_right] using congrArg (fun A : Subgroup G => A.subgroupOf H) hXH
  have hXM₂ : M.subgroupOf X = B.subgroupOf X := by
    simpa only [inf_subgroupOf_left] using congrArg (fun A : Subgroup G => A.subgroupOf X) hXM
  have hXH₂ : H.subgroupOf X = P.subgroupOf X := by
    simpa only [inf_subgroupOf_left] using congrArg (fun A : Subgroup G => A.subgroupOf X) hXH
  refine ⟨LocalGeometry.normalizer_quotient_of_ordinary_at h structural D m eL hM,hH,?_,?_,?_,?_⟩
  · change Quasithin.I5.RankTwoParabolics M _ _ _
    rw [hXM₁]
    exact hp
  · change Quasithin.I5.RankTwoParabolics H _ _ _
    rw [hXH₁]
    exact hl
  · change Quasithin.I5.RankTwoParabolics X _ _ _
    rw [hXM₂,hXH₂]
    exact hplane
  · change M ⊓ H ⊓ X = (T : Subgroup G)
    calc
      M ⊓ H ⊓ X = (X ⊓ H) ⊓ (X ⊓ M) := by simp only [inf_assoc,inf_left_comm,inf_comm,inf_idem]
      _ = P ⊓ B := by rw [hXH,hXM]
      _ = (T : Subgroup G) := hi


/-- Transport the three constructed residues into the actual generated
subgroup. The fixed line and maximal-local uniqueness supply D4 and D5. -/
theorem markedC3_of_original_residues_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (X : Subgroup G)
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hpoint : Nonempty ((normalizer (L : Set G) ⧸ pCore 2 (normalizer (L : Set G))) ≃*
        alternatingGroup (Fin 6)) ∨
      Nonempty ((normalizer (L : Set G) ⧸ pCore 2 (normalizer (L : Set G))) ≃* Equiv.Perm (Fin 6)))
    (hline : Nonempty ((centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hplane : Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL))
    (hp : RankTwoParabolics (normalizer (L : Set G))
      ((T : Subgroup G).subgroupOf (normalizer (L : Set G)))
      ((centralizer ({z} : Set G)).subgroupOf (normalizer (L : Set G)))
      (X.subgroupOf (normalizer (L : Set G))))
    (hl : RankTwoParabolics (centralizer ({z} : Set G))
      ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G)))
      ((normalizer (L : Set G)).subgroupOf (centralizer ({z} : Set G)))
      (X.subgroupOf (centralizer ({z} : Set G))))
    (hr : RankTwoParabolics X ((T : Subgroup G).subgroupOf X)
      ((normalizer (L : Set G)).subgroupOf X) ((centralizer ({z} : Set G)).subgroupOf X))
    (hch : normalizer (L : Set G) ⊓ centralizer ({z} : Set G) ⊓ X = (T : Subgroup G)) :
    Nonempty (MarkedC3 T L z X) := by
  let M := normalizer (L : Set G)
  let H := centralizer ({z} : Set G)
  let E := generated M z X
  let F : Fin 3 → Subgroup E := ![M.subgroupOf E,H.subgroupOf E,X.subgroupOf E]
  have hME : M ≤ E := first_le_generated _ _ _
  have hHE : H ≤ E := le_sup_of_le_left le_sup_right
  have hXE : X ≤ E := le_sup_right
  have hTE : (T : Subgroup G) ≤ E := D.sylow_normalizes_component.trans hME
  have hc : chamberSubgroup F = (T : Subgroup G).subgroupOf E := by
    ext x
    constructor
    · intro hx
      have hh := mem_iInf.mp hx
      exact hch.le ⟨⟨hh 0,hh 1⟩,hh 2⟩
    · intro hx
      have hh := hch.ge hx
      apply mem_iInf.mpr
      intro i
      fin_cases i
      · exact hh.1.1
      · exact hh.1.2
      · exact hh.2
  let e0 : F 0 ≃* M := subgroupOfEquivOfLe hME
  let e1 : F 1 ≃* H := subgroupOfEquivOfLe hHE
  let e2 : F 2 ≃* X := subgroupOfEquivOfLe hXE
  have hp' := hp.comap_surjective e0.toMonoidHom e0.surjective
  have hl' := hl.comap_surjective e1.toMonoidHom e1.surjective
  have hr' := hr.comap_surjective e2.toMonoidHom e2.surjective
  have hpF : RankTwoParabolics (F 0) ((chamberSubgroup F).subgroupOf (F 0))
      (localParabolic F 0 1) (localParabolic F 0 2) := by
    rw [hc]
    exact hp'
  have hlF : RankTwoParabolics (F 1) ((chamberSubgroup F).subgroupOf (F 1))
      (localParabolic F 1 0) (localParabolic F 1 2) := by
    rw [hc]
    exact hl'
  have hrF : RankTwoParabolics (F 2) ((chamberSubgroup F).subgroupOf (F 2))
      (localParabolic F 2 0) (localParabolic F 2 1) := by
    rw [hc]
    exact hr'
  have hgen : (⨆ i, F i) = ⊤ := by
    apply map_injective E.subtype_injective
    rw [Subgroup.map_iSup,←MonoidHom.range_eq_map,range_subtype]
    apply le_antisymm (iSup_le fun _ => map_subtype_le _)
    change (M ⊔ H) ⊔ X ≤ _
    refine sup_le (sup_le ?_ ?_) ?_
    · apply le_iSup_of_le (0 : Fin 3)
      change M ≤ (M.subgroupOf E).map E.subtype
      rw [map_subgroupOf_eq_of_le hME]
    · apply le_iSup_of_le (1 : Fin 3)
      change H ≤ (H.subgroupOf E).map E.subtype
      rw [map_subgroupOf_eq_of_le hHE]
    · apply le_iSup_of_le (2 : Fin 3)
      change X ≤ (X.subgroupOf E).map E.subtype
      rw [map_subgroupOf_eq_of_le hXE]
  have hcenter : center (F 0) ≠ ⊥ := by
    intro he
    apply normalizer_center_ne_bot_at h structural D m
    apply le_bot_iff.mp
    intro a ha
    have hz : e0.symm a ∈ center (F 0) := (centerCongr e0.symm ⟨a,ha⟩).property
    rw [he,mem_bot] at hz
    exact mem_bot.mpr (e0.symm.injective (hz.trans (map_one e0.symm).symm))
  obtain ⟨eH⟩ := hline
  obtain ⟨eX⟩ := hplane
  let S : DSystem .C3 E := {
    family := F
    finite_vertex := fun _ => inferInstance
    point_A3 := fun he => nomatch he
    point_C3 := fun _ => hpoint.imp
      (fun ⟨e⟩ => ⟨(QuotientGroup.congr _ _ e0 (pCore_map_iso 2 e0)).trans e⟩)
      (fun ⟨e⟩ => ⟨(QuotientGroup.congr _ _ e0 (pCore_map_iso 2 e0)).trans e⟩)
    line_quotient := ⟨(QuotientGroup.congr _ _ e1 (pCore_map_iso 2 e1)).trans eH⟩
    plane_quotient := ⟨(QuotientGroup.congr _ _ e2 (pCore_map_iso 2 e2)).trans eX⟩
    sylow := by
      intro i
      let R := T.subtype hTE
      have ht : (R : Subgroup E) ≤ F i := by
        rw [Sylow.coe_subtype,←hc]
        exact iInf_le _ i
      exact ⟨R.subtype ht,by rw [Sylow.coe_subtype,hc]; rfl⟩
    point_parabolics := hpF
    line_parabolics := hlF
    plane_parabolics := hrF
    generate := hgen
    core_free := by rw [hc]; exact original_chamber_core_eq_bot_at h structural z X hout
    nondegenerate := fun _ => Or.inl hcenter }
  exact ⟨{ system := S, first := rfl, second := rfl, third := rfl, chamber := hc }⟩


/-- Construct the marked C₃ system on the original generated subgroup and
recognize that subgroup as Sp₆(2). The L₃(2) third-vertex quotient remains
the explicit earlier 13.4.7 input; ambient recognition still needs fusion. -/
theorem original_R1_marked_geometry_at
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
      L ⊔ (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)))
    (hthird :
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let X := (I ⊔ (T : Subgroup G)) ⊔ B
      Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
    let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
    let X := (I ⊔ (T : Subgroup G)) ⊔ B
    Nonempty (MarkedC3 T L z.val X) ∧
      Nonempty (generated (normalizer (L : Set G)) z.val X ≃*
        Theory.SpecificGroups.SymplecticSix.Sp (ZMod 2)) := by
  let H := centralizer ({z.val} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  let X := (I ⊔ (T : Subgroup G)) ⊔ B
  obtain ⟨hM,hH,hp,hl,hr,hch⟩ := original_R1_three_residues_at h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342 W hW hT hgenerate hsupp hthird
  obtain ⟨C⟩ := markedC3_of_original_residues_at h structural D m z.val X hout
    hM hH hthird hp hl hr hch
  exact ⟨⟨C⟩,⟨Quasithin.I5.C3Recognition.equivSp6 C.system⟩⟩


/-- Apply the original local product and constructed chamber to the checked
fusion and commuting-product arguments. Only earlier amalgam conclusions
remain: the actual third quotient, Thompson normality and overgroup supplement. -/
theorem isPSp_of_original_R1_and_amalgam_conclusions_at
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
      L ⊔ (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)))
    (hthird :
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let X := (I ⊔ (T : Subgroup G)) ⊔ B
      Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL))
    (hnormal :
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      (I ⊔ (T : Subgroup G)) ⊔ B ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (supplement :
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let X := (I ⊔ (T : Subgroup G)) ⊔ B
      ∀ Y : Subgroup G, Y ∈ Chapter1.HOver G (X : Set G) →
        (Y : Set G) = (X : Set G) *
          (Y ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X : Set G) : Subgroup G)) :
    ClassicalGroup.IsPSp G 3 2 := by
  obtain ⟨⟨C⟩,_⟩ := original_R1_marked_geometry_at h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342 W hW hT hgenerate hsupp hthird
  exact isPSp_of_source_marked_chamber_at h₀ h structural D m z.val _ C hnormal supplement

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
