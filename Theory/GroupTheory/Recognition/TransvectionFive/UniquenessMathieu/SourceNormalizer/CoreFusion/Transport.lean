module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.CoreFusion.Model
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Boundary
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCoordinates

/-!
# The source second involution class is disjoint from the marked class

Transport the actual two-core through the full centralizer marking. The
local normal form sends its non-root involutions to the rank-two element
with rectangle code 33. In the 21-point branch the checked fusion census
contains exactly the rank-one locus, so no such involution is fused to z.
This proves the needed source 39.4 exclusion directly from the measured
Mathieu branch and completes the missing input to 40.4(2).

The internal import of `UniquenessLinearSourcePlaneCoordinates` is used only
for the private code-33 matrix bridge. It keeps the shared decoder's public
boundary unchanged and retains exactly its established coordinate convention.

Source: Aschbacher, *Sporadic Groups* (1994), 39.1(5), 39.4 and 40.3–40.4,
printed pp.213–218.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear UniquenessLinear.PlaneTensor
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

private theorem representative_matrix :
    (modelPlaneCoordinates.symm (Multiplicative.ofAdd (decode 33)) : SL).val =
      CoreFusion.entries CoreFusion.representative := by
  rw [modelPlaneCoordinates_matrix, modelPlaneCoordinates.apply_symm_apply]
  decide +kernel

omit [Finite G] in
/-- A non-root involution in the literal point two-core is conjugate inside
C_G(z) to the rank-two rectangle element with marked code 33. -/
theorem core_involution_conjugate (q : G)
    (hq : q ∈ (Subgroup.centralizer ({z} : Set G)).pCoreIn 2)
    (horder : orderOf q = 2) (hr : q ∉ F.row) (hc : q ∉ F.column) :
    ∃ c : Subgroup.centralizer ({z} : Set G),
      (c : G) * q * (c : G)⁻¹ = element F 33 := by
  let H := Subgroup.centralizer ({z} : Set G)
  let qH : H := ⟨q,pCoreIn_le 2 H hq⟩
  let qM := F.equiv qH
  have hqH : qH ∈ pCore 2 H := by
    obtain ⟨v,hv,hvq⟩ := hq
    exact (show v = qH from Subtype.ext hvq) ▸ hv
  have hqM : qM ∈ pCore 2 centralizer :=
    pCore_map_iso 2 F.equiv ▸ mem_map_of_mem F.equiv.toMonoidHom hqH
  have hs : (qM : SL) ^ 2 = 1 := by
    have hq2 : q ^ 2 = 1 := horder ▸ pow_orderOf_eq_one q
    have hh : qH ^ 2 = 1 := Subtype.ext hq2
    have hm := congrArg (fun h : H => (F.equiv h : SL)) hh
    simpa only [map_pow, map_one,Subgroup.coe_pow,Subgroup.coe_one] using hm
  have hrM : (qM : SL) ∉ Model.row := fun h => hr ((F.mem_pullback_iff Model.row qH).mpr h)
  have hcM : (qM : SL) ∉ Model.column := fun h => hc ((F.mem_pullback_iff Model.column qH).mpr h)
  obtain ⟨c,hc⟩ := CoreFusion.core_involution_conjugator qM hqM hs hrM hcM
  have he : (c : SL) * (qM : SL) * (c : SL)⁻¹ =
      (modelPlaneCoordinates.symm (Multiplicative.ofAdd (decode 33)) : SL) :=
    Subtype.ext (hc.trans representative_matrix.symm)
  refine ⟨F.equiv.symm c, ?_⟩
  have hh : F.equiv.symm c * qH * (F.equiv.symm c)⁻¹ =
      (⟨element F 33,F.pullback_le _ (element_mem F 33)⟩ : H) := by
    apply F.equiv.injective
    apply Subtype.ext
    simpa only [map_mul,map_inv,F.equiv.apply_symm_apply,element_model,
      Subgroup.coe_mul,Subgroup.coe_inv] using he
  exact congrArg (fun h : H => (h : G)) hh

/-- Source 39.4's fusion exclusion in the Mathieu branch: the actual
non-root involutions in O₂(C_G(z)) are not conjugate to z. The proof uses
the explicit local orbit and the already checked 21-point fusion census. -/
theorem secondInvolutionClass_not_fused (hcounts : MathieuFusionOrientation F)
    (t : G) (ht : SecondInvolutionClass F t) : ¬ IsConj z t := by
  obtain ⟨q,hq,ho,hr,hc,hqt⟩ := ht
  obtain ⟨c,he⟩ := core_involution_conjugate F q hq ho hr hc
  have hrep : IsConj q (element F 33) := isConj_iff.mpr ⟨c,he⟩
  intro hzt
  have hf := (plane_fusion_iff_pure F hcounts.1 33).mp (hzt.trans (hqt.symm.trans hrep))
  exact (by decide : PlaneCensus.pure (33 : PlaneCensus.Code) ≠ true) hf

omit [Finite G] in
/-- Membership in the source second class retains nonidentity, by its
actual conjugacy to an involution. -/
theorem secondInvolutionClass_ne_one (t : G) (ht : SecondInvolutionClass F t) : t ≠ 1 := by
  obtain ⟨q,_,ho,_,_,hqt⟩ := ht
  intro ht1
  rw [ht1, isConj_one_left] at hqt
  simp [hqt] at ho

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
