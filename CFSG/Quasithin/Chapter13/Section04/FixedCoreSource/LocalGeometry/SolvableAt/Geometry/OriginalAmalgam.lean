module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Geometry.Amalgam
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.CoveredSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.FirstFlagCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalAmalgam
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.Amalgam
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.ThompsonNormalizer

/-!
# The literal L₂T application in the solvable source amalgam: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/Geometry/OriginalAmalgam` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The full Z_L has centralizer M once M=LT; no equality Z_L=C_V(L)
is used before the amalgam theorem establishes the central rank. -/
theorem original_omega_fixed_centralizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G)) :
    centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (L : Set G) : Subgroup G) : Set G) = normalizer (L : Set G) := by
  have hf : V ⊓ centralizer (L : Set G) ≤
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) :=
    le_inf (LocalGeometry.fixed_le_original_omegaCenter_at h structural D m) inf_le_right
  apply le_antisymm
  · exact (centralizer_le hf).trans (fixed_centralizer_eq_normalizer_at h structural D m).le
  · rw [hM]
    refine sup_le (le_centralizer_iff.mpr inf_le_right) ?_
    intro t ht v hv
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hv.1).2.2 t ht).symm

theorem original_solvable_amalgam_inputs_at
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
    (L₂ : Subgroup G) (hL₂ : L₂ ≤ L)
    (hmax₂ : IsCoatom ((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))))
    (hres₂ :
      (pResidual 2 (L₂ ⊔ (T : Subgroup G) : Subgroup G)).map (L₂ ⊔ (T : Subgroup G)).subtype = L₂)
    (hgenerate : (firstCentralizerResidual L z.val ⊔ (T : Subgroup G)) ⊔
      (L₂ ⊔ (T : Subgroup G)) = L ⊔ (T : Subgroup G))
    (hfixed₂ : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L₂ : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G))
    (hsupp : normalizer (L : Set G) =
      L ⊔ (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G))) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
    let P := I ⊔ (T : Subgroup G)
    let B := L₂ ⊔ (T : Subgroup G)
    let H₀ := P ⊔ B
    let K₁ := (pResidual 2 P).map P.subtype
    let C₁ := H₀ ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (K₁ : Set G) : Subgroup G) : Set G)
    let C₂ := H₀ ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (L₂ : Set G) : Subgroup G) : Set G)
    normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
      ¬ ⁅K₁,L₂⁆ ≤ K₁.pCoreIn 2 ∧
      (H₀ ∈ Chapter1.H G →
        H₀ ⊓ normalizer (L : Set G) = B ∧ H₀ ⊓ H = P ∧
        C₁ = P ∧ C₂ = B ∧ (K₁.subgroupOf C₁).Normal ∧ (L₂.subgroupOf C₂).Normal ∧
        (primeToResidual 3 C₁).map C₁.subtype = K₁) := by
  obtain ⟨_,_,_,_,_,hinter,_,_,_⟩ := centralizer_pair_quotient_of_original_R1_at
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  have hM := normalizer_eq_component_sylow_of_centralizer_intersection hsupp hinter
  let B := L₂ ⊔ (T : Subgroup G)
  have hBM : B ≤ normalizer (L : Set G) :=
    sup_le (hL₂.trans L.le_normalizer) D.sylow_normalizes_component
  have hmaxM : IsCoatom (B.subgroupOf (normalizer (L : Set G))) := by
    rw [hM]
    exact hmax₂
  have hgen : (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G) := by
    change (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)) ⊔
      (L₂ ⊔ (T : Subgroup G)) = normalizer (L : Set G)
    rw [hinter,hgenerate,hM]
  have hfixed : centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer ((pResidual 2 B).map B.subtype : Set G) : Subgroup G) : Set G) =
        normalizer (L : Set G) := by
    change centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer ((pResidual 2 (L₂ ⊔ (T : Subgroup G) : Subgroup G)).map
        (L₂ ⊔ (T : Subgroup G)).subtype : Set G) : Subgroup G) : Set G) = _
    rw [hres₂,hfixed₂]
    exact original_omega_fixed_centralizer_at h structural D m hM
  have hex := original_R1_excludes_amalgam_product_at h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342 B le_sup_right hgen
  have hcen := original_R1_amalgam_centralizers_at h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342 B hBM hmaxM hgen hfixed
  dsimp only at hex hcen ⊢
  change (pResidual 2 B).map B.subtype = L₂ at hres₂
  rw [hres₂] at hex hcen
  exact ⟨hM,hex,hcen⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
