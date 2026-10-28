module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PResidual.PerfectCover
/-!
# Literal local residual containment from the five-point action

Restrict the normalizer action to the two-residual of the vector centralizer.
Its image is alternating and two-perfect, so the existing stabilizer calculation
places it in the cubic image of L_v. Matching that cubic element lifts each
residual element into L_v C_M(V). This is the exact residual map required in
13.6.18; the assumed local normalization is supplied by 13.6.5.
Source: Aschbacher--Smith 13.2.3,13.6.5,18, printed pp.878,927,931.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

omit [Finite G] in
theorem FlagSource.normalizerAction_kernel_centralizes
    (d : FlagSource T L V V₁ V₂) (n : normalizer (V : Set G))
    (hn : d.normalizerAction n = 1) : (n : G) ∈ centralizer (V : Set G) := by
  apply mem_centralizer_iff.mpr
  intro y hy
  obtain ⟨w,rfl⟩ := d.module.range_eq.ge hy
  have he := d.normalizer_equivariant n w.toAdd
  rw [hn,map_one,Module.End.one_apply] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

theorem FlagSource.local_residual_le
    (d : FlagSource T L V V₁ V₂) (M : Subgroup G)
    (hLM : L ≤ M)
    (hMN : Mv M (markedV d.module) ≤ normalizer (V : Set G)) :
    (pResidual 2 (Mv M (markedV d.module))).map (Mv M (markedV d.module)).subtype ≤
      Lv L (markedV d.module) ⊔ (M ⊓ centralizer (V : Set G)) := by
  let H := Mv M (markedV d.module)
  let R := pResidual 2 H
  let q := d.normalizerAction.comp (inclusion hMN)
  have heven (r : R) : q r.val ∈ alternatingGroup (Fin 5) := by
    rw [←Equiv.Perm.twoResidual_eq_alternating]
    exact map_pResidual_le 2 q (mem_map_of_mem q r.property)
  let f : R →* alternatingGroup (Fin 5) :=
    (q.comp R.subtype).codRestrict _ heven
  have hfixed (r : R) : act (f r) v = v := by
    apply Multiplicative.ofAdd.injective
    apply d.module.injective
    have he := d.normalizer_equivariant
      (inclusion hMN r.val) v
    change MulAut.conj (r.val.val : G) (markedV d.module) =
      d.module.map (Multiplicative.ofAdd (act (f r) v)) at he
    rw [←he]
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp r.val.property.2)
  let fs : R →* ResidualCoordinates.stabilizer := f.codRestrict _ hfixed
  have hcubic (r : R) : f r ∈ ResidualCoordinates.cubicGroup := by
    have ht : r ∈ pResidual 2 R := by
      rw [(pResidual_eq_top_iff 2 R).mpr (isPPerfect_pResidual 2)]
      exact mem_top _
    have hst : fs r ∈ pResidual 2 ResidualCoordinates.stabilizer := by
      exact map_pResidual_le 2 fs (mem_map_of_mem fs ht)
    have hci : fs r ∈ ResidualCoordinates.cubicInStabilizer :=
      ResidualCoordinates.residual_le_cubic hst
    exact hci
  rintro x ⟨r,hr,rfl⟩
  let r' : R := ⟨r,hr⟩
  obtain ⟨l,hl⟩ := residualCubicAction_surjective d.module ⟨f r',hcubic r'⟩
  have he : (residualAction d.module l).val = q r :=
    congrArg (fun a : ResidualCoordinates.cubicGroup => a.val.val) hl
  have hlN : (l : G) ∈ normalizer (V : Set G) :=
    d.module.normalizes (residual_le_L d.module l.property)
  have hlM : (l : G) ∈ M := hLM (residual_le_L d.module l.property)
  let c : normalizer (V : Set G) :=
    ⟨(l : G)⁻¹ * (r : G),mul_mem (inv_mem hlN) (hMN r.property)⟩
  have hc : d.normalizerAction c = 1 := by
    change d.normalizerAction
      ((⟨l,hlN⟩ : normalizer (V : Set G))⁻¹ * inclusion hMN r) = 1
    rw [map_mul,map_inv,d.action_agrees ⟨l,residual_le_L d.module l.property⟩ hlN]
    change (residualAction d.module l).val⁻¹ * q r = 1
    rw [he,inv_mul_cancel]
  have hcM : (c : G) ∈ M := M.mul_mem (M.inv_mem hlM) r.property.1
  have hcC := d.normalizerAction_kernel_centralizes c hc
  have hprod := (Lv L (markedV d.module) ⊔ (M ⊓ centralizer (V : Set G))).mul_mem
    (mem_sup_left l.property) (mem_sup_right ⟨hcM,hcC⟩)
  change (r : G) ∈ Lv L (markedV d.module) ⊔ (M ⊓ centralizer (V : Set G))
  simpa only [c,mul_inv_cancel_left] using hprod
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
