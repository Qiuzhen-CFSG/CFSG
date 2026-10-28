module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicNormalizerFactorGeometry
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.PointwiseSingularPlane

/-! The chosen elementary factor cuts out a singular plane in U/Z(U).
Its pointwise terminal stabilizer is the order-two image of the factor.
Source: Aschbacher–Smith 14.3.19, the automizer calculation. -/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem elementary_factor_pointwise_terminal_stabilizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (dg : ClosureGeometry F) (hZ : F.ZU=F.Vi 1) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤)
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2) (hAH:A≤F.H)
    (hVA:rankTwoSeed T M≤A) (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (a:G) (ha:a∈A) (haU:a∉F.U) :
    ∀b:F.H,(∀u:F.U,(u:G)∈A→(b:G)*(u:G)=(u:G)*(b:G))→
      QuotientGroup.mk' F.terminalHatAction.ker b=1 ∨
      QuotientGroup.mk' F.terminalHatAction.ker b=
        QuotientGroup.mk' F.terminalHatAction.ker ⟨a,hAH ha⟩ := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let C := A⊓F.U
  have hnotCV:¬C≤rankTwoSeed T M := by
    intro hc
    have hh:=card_le_of_le hc
    have hv:Nat.card (rankTwoSeed T M)=4 := by
      simpa only [F.last,show (2:ℕ)^2=4 from rfl] using F.card 2 le_rfl
    rw [hc8,hv] at hh
    omega
  obtain ⟨x,hx,hxV⟩ := SetLike.not_le_iff_exists.mp hnotCV
  have hxA:x∈A := hx.1
  have hxU:x∈F.U := hx.2
  have hVC:rankTwoSeed T M≤C :=
    le_inf hVA (le_conjugateSpanBy _ _)
  have hdim:2≤finrank (ZMod 2) (hatSpace F C) := by
    have hv:finrank (ZMod 2) (hatSpace F (rankTwoSeed T M))=1 :=
      (congrArg (fun B:Subgroup G=>finrank (ZMod 2) (hatSpace F B)) F.last).symm.trans
        (finrank_hatSpace_plane F (by decide) dg.seed_center)
    have hl:hatSpace F (rankTwoSeed T M)≤hatSpace F C := by
      rintro v ⟨u,hu,rfl⟩
      exact ⟨u,hVC hu,rfl⟩
    by_contra hb
    have heq:hatSpace F (rankTwoSeed T M)=hatSpace F C :=
      Submodule.eq_of_le_of_finrank_le hl (by omega)
    let u:F.U:=⟨x,hxU⟩
    have hu:Additive.ofMul (QuotientGroup.mk' (center F.U) u)∈hatSpace F C :=
      ⟨u,⟨hxA,hxU⟩,rfl⟩
    rw [←heq] at hu
    obtain ⟨v,hv,he⟩:=hu
    have hk:v⁻¹*u∈center F.U := by
      apply (QuotientGroup.eq_one_iff (N:=center F.U) (v⁻¹*u)).mp
      change QuotientGroup.mk' (center F.U) (v⁻¹*u)=1
      rw [map_mul,map_inv,he]
      exact inv_mul_cancel _
    have hz:((v⁻¹*u:F.U):G)∈rankTwoSeed T M :=
      (show F.ZU≤rankTwoSeed T M from hZ ▸ F.le_seed 1) ⟨v⁻¹*u,hk,rfl⟩
    have hh := (rankTwoSeed T M).mul_mem hv hz
    change (v:G)*((v:G)⁻¹*x)∈rankTwoSeed T M at hh
    exact hxV (by simpa only [mul_inv_cancel_left] using hh)
  have hdis:Disjoint (conjugate (F.Vi 1) g) F.ZU :=
    disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) (sourceResidual M Mc)
      h.L_normalizes_seed dg.seed_center g hgP hgH).1
  obtain ⟨_,hQ,hnd⟩ := quadratic_intersection_of_center_point F dg (by decide) hZ g hdis
  have hs:∀v∈hatSpace F C,centerPointQuadraticForm F dg (by decide) hZ v=0 := by
    intro v hv
    obtain ⟨u,hu,he⟩ := (show v.toMul∈hatImage F C from hv)
    have hp:u^2=1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (A:=A) (u:G) hu.1)
    have he1:F.uhatSquare dg.two (center_frattini_bot_of_center_point F dg hZ)
      (QuotientGroup.mk' (center F.U) u)=1 := by
      apply Subtype.ext
      rw [F.uhatSquare_apply_mk,hp]
      rfl
    change centerPointQuadraticForm F dg (by decide) hZ (Additive.ofMul v.toMul)=0
    rw [←he]
    rw [centerPointQuadraticForm,F.uhatQuadraticForm_apply,he1]
    simp only [map_one]
    rfl
  let aH:F.H := ⟨a,hAH ha⟩
  let q:=QuotientGroup.mk' F.terminalHatAction.ker
  have haQ:a∉F.H.pCoreIn 2 := by
    intro hh
    have hRQ := (parabolic_core_intersection_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
    have hw:a∈F.W := hRQ ▸ (show a∈(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊓F.H.pCoreIn 2 from ⟨hAR ha,hh⟩)
    exact haU hw.1
  have had:q aH≠1 := by
    intro hh
    have hk:aH∈F.terminalHatAction.ker := (QuotientGroup.eq_one_iff _).mp hh
    rw [terminal_kernel_of_center_point F dg hZ] at hk
    exact haQ (mem_map_of_mem F.H.subtype hk)
  have hi:∀v∈hatSpace F C,F.terminalRepresentation (q aH) v=v := by
    rintro v ⟨u,hu,rfl⟩
    change F.terminalRepresentation (q aH) (Additive.ofMul (QuotientGroup.mk' (center F.U) u)) =
      Additive.ofMul (QuotientGroup.mk' (center F.U) u)
    apply Additive.toMul.injective
    change F.terminalHatAction aH (QuotientGroup.mk' (center F.U) u)=QuotientGroup.mk' (center F.U) u
    rw [F.terminalHatAction_apply_mk]
    apply congrArg (QuotientGroup.mk' (center F.U))
    apply Subtype.ext
    change a*(u:G)*a⁻¹=(u:G)
    have hh:a*(u:G)=(u:G)*a := congrArg Subtype.val
      (mul_comm (⟨a,ha⟩:A) ⟨u,hu.1⟩)
    rw [hh,mul_inv_cancel_right]
  have hform:∀t v,centerPointQuadraticForm F dg (by decide) hZ
      (F.terminalRepresentation t v)=centerPointQuadraticForm F dg (by decide) hZ v := by
    intro t v
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker t
    exact hQ b v.toMul
  intro b hb
  apply ChapterG.Section09.FittingRecognition.Four.pointwise_stabilizer_of_full_orthogonal
    F.terminalRepresentation hr (centerPointQuadraticForm F dg (by decide) hZ) hnd hform
    (q aH) had (hatSpace F C) hdim hs hi (q b)
  rintro v ⟨u,hu,rfl⟩
  apply Additive.toMul.injective
  change F.terminalHatAction b (QuotientGroup.mk' (center F.U) u)=
    QuotientGroup.mk' (center F.U) u
  rw [F.terminalHatAction_apply_mk]
  apply congrArg (QuotientGroup.mk' (center F.U))
  apply Subtype.ext
  change (b:G)*(u:G)*(b:G)⁻¹=(u:G)
  rw [hb u hu.1,mul_inv_cancel_right]
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
