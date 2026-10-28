module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.OriginalMaximality
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ActorRankIntersection

/-!
# Sylow movement of the original elementary factors

An elementary factor containing an involution in W outside V meets the
actual U in a singular section strictly larger than the seed. If T
normalized that factor, its image in U/Z(U) would be a Sylow-invariant
singular plane, contradicting the full orthogonal action. Thus T moves the
factor to the other maximal elementary factor.

Source: Aschbacher--Smith 14.3.18(4), printed p.996.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem elementary_factor_not_sylow_normalized_of_full_orthogonal
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
    (dg : ClosureGeometry F) (hZ : F.ZU=F.Vi 1) (_hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤)
    (A:Subgroup G) [IsElementaryAbelian 2 A] (hVA:rankTwoSeed T M≤A)
    (x:G) (hxA:x∈A) (hxU:x∈F.U) (hxV:x∉rankTwoSeed T M) :
    ¬(T:Subgroup G)≤normalizer (A:Set G) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let C := A⊓F.U
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
  intro hTA
  have hTC:(T:Subgroup G)≤normalizer (C:Set G) :=
    (le_inf hTA ((F.invariant 1).trans (le_normalizer_conjugateSpanBy _ _))).trans
      inf_normalizer_le_normalizer_inf
  let P:Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (f:=QuotientGroup.mk' F.terminalHatAction.ker) (QuotientGroup.mk'_surjective _)
  have hi:∀t∈(P:Subgroup F.TerminalHdot),∀v∈hatSpace F C,
      F.terminalRepresentation t v∈hatSpace F C :=
    F.terminal_hatSpace_invariant C (T:Subgroup G) hTC
  have hform:∀t v,centerPointQuadraticForm F dg (by decide) hZ
      (F.terminalRepresentation t v)=centerPointQuadraticForm F dg (by decide) hZ v := by
    intro t v
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker t
    exact hQ a v.toMul
  obtain ⟨D,hDn,hDc⟩ := ChapterG.Section09.FittingRecognition.Four.normal_cubic_of_orthogonal_singular_plane
    F.terminalRepresentation ⊤ le_top hr (centerPointQuadraticForm F dg (by decide) hZ)
    hnd hform P (hatSpace F C) hdim hs hi
  let := hDn
  exact no_normal_cubic_of_center_point hG T hempty hM hu hmany hcard e hnot F dg hZ D hDc

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
