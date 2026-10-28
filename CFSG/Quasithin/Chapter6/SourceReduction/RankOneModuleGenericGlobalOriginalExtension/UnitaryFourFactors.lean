module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourReduced
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFactors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5LocalFactorization
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.PCoreRestriction

/-!
# Original U₄ residuals and the exact outer Sylow index

Restrict the supplied original endpoint maps to their solvable residuals.
The faithful left factor excludes the point endpoint, so the original factors
are the native plane and point residuals and n=2m. The normalized right Borel
then gives S=O₂(RS)(T∩L). Relative core restriction identifies the intersection
with O₂(RS) as O₂(R), hence [S:T∩L]=[O₂(RS):O₂(R)] and the join-core has
order q⁵[S:T∩L]. The core enlargement is retained, including the possible
degree-two extension; neither S=T nor R=O²(H) is assumed.

These calculations precede the remaining native outer-action bound. The
adjacent action module and Chapter 12 consumer retain the same original
marking. DGS exhaustiveness, uniqueness and unconditional GlobalExit assembly
remain separate obligations. The private native center and residual proofs
reuse the calculations in `RankOneModuleGenericGlobalUnitaryFactors`.
Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6--7, pp.650--651
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
namespace OriginalUnitaryFour
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
section MatrixCenter
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "R" => radical F σ hσ
local notation "L" => localSU F (form F σ hσ)
local notation "κ" => coordinatesOfRadical F σ hσ

omit [Finite F] in
private theorem center_radical_central (hnt : ∃ u, σ u ≠ u) :
    (center R).map (radical F σ hσ).subtype ≤ center L := by
  rintro x ⟨r,hr,rfl⟩
  obtain ⟨hx,hy⟩ := (mem_center_radical_iff F σ hσ hnt r).mp hr
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  have hmat : r.val.val.val.val = radicalMatrix F σ (κ r) := by
    exact congrArg (fun x : R => x.val.val.val.val)
      ((radicalCoordinatesEquiv F σ hσ).apply_symm_apply r).symm
  have hg := (mem_localSU F _ g.val).mp g.property
  have hl := last_row F σ hσ g.val g.property
  change g.val.val.val * r.val.val.val.val = r.val.val.val.val * g.val.val.val
  rw [hmat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalMatrix, hx,hy, Matrix.mul_apply, Fin.sum_univ_succ,
      hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,hl.2.1,hl.2.2.1,hl.2.2.2,add_comm]


end MatrixCenter

private theorem core_center_transport
    {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hc : (center (pCore 2 X)).map (pCore 2 X).subtype ≤ center X) :
    (center (pCore 2 Y)).map (pCore 2 Y).subtype ≤ center Y := by
  let c := (e.subgroupMap (pCore 2 X)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  rw [←center_map_equiv c,Subgroup.map_map,←center_map_equiv e]
  change (center (pCore 2 X)).map (e.toMonoidHom.comp (pCore 2 X).subtype) ≤ _
  rw [←Subgroup.map_map]
  exact map_mono hc

/-- The point residual centralizes the center of its own two-core. -/
private theorem point_core_center_central (m : ℕ) (hm : 1 ≤ m) :
    (center (pCore 2 (PointLocal.ProjectiveLocal m hm))).map
      (pCore 2 (PointLocal.ProjectiveLocal m hm)).subtype ≤
        center (PointLocal.ProjectiveLocal m hm) := by
  apply core_center_transport (PointLocal.localEquiv m hm)
  rw [←PointLocal.radical_eq_twoCore m hm]
  exact center_radical_central (MatrixField m) (fieldConj m)
    (fieldConj_involutive m hm) (PointLocal.fieldConj_nontrivial m hm)

private theorem plane_parabolic_residual (m : ℕ) (hm : 1 ≤ m) :
    (solvableResidual (planeParabolic m hm)).map (planeParabolic m hm).subtype = L2 m hm := by
  let := L2_isPerfect m hm
  open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneLocal in
  have hmat : (solvableResidual (planeParabolicMatrix m hm)).map
      (planeParabolicMatrix m hm).subtype = L2Matrix m hm := by
    let f := planeDet (MatrixField m) (standardForm m hm)
    have hle : solvableResidual (planeParabolicMatrix m hm) ≤ f.ker := by
      apply (Subgroup.map_eq_bot_iff _).mp
      exact bot_unique ((map_solvableResidual_le f).trans (solvableResidual_eq_bot.le))
    apply le_antisymm (map_mono hle)
    change L2Matrix m hm ≤ _
    let : Group.IsPerfect (L2Matrix m hm) :=
      Group.IsPerfect.ofSurjective (f := (L2ProjectIso m hm).symm.toMonoidHom)
        (L2ProjectIso m hm).symm.surjective
    exact le_map_solvableResidual_of_isPerfect _ _ (L2Matrix_le_planeParabolic m hm)
  let e : planeParabolicMatrix m hm ≃* planeParabolic m hm :=
    (planeParabolicMatrix m hm).equivMapOfInjective (projection m hm) (projection_injective m hm)
  rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,Subgroup.map_map]
  change (solvableResidual (planeParabolicMatrix m hm)).map
    ((projection m hm).comp (planeParabolicMatrix m hm).subtype) = _
  rw [←Subgroup.map_map,hmat]
  rfl

end OriginalUnitaryFour

namespace Preparation
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (e : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))

/-- Restriction of the original left map to its actual selected residual. -/
def originalUnitaryFourLeftEquiv : L ≃* OriginalUnitaryFour.nativeResidual m hm point := by
  let P := OriginalUnitaryFour.endpoint m hm point
  let j : P →* MulAut (ProjectiveGroup m hm) := MulAut.conj.comp P.subtype
  have hj : Function.Injective j :=
    (ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm).comp P.subtype_injective
  let a := d.originalEndpointResidualEquiv h hTH hp 0 e.left e.left_injective j hj
    (by simpa only [map_map] using e.left_residual)
  exact a.trans ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective)

/-- Restriction of the original right map to its actual selected residual. -/
def originalUnitaryFourRightEquiv : R ≃* OriginalUnitaryFour.nativeResidual m hm (!point) := by
  let P := OriginalUnitaryFour.endpoint m hm (!point)
  let j : P →* MulAut (ProjectiveGroup m hm) := MulAut.conj.comp P.subtype
  have hj : Function.Injective j :=
    (ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm).comp P.subtype_injective
  let a := d.originalEndpointResidualEquiv h hTH hp 1 e.right e.right_injective j hj
    (by simpa only [map_map] using e.right_residual)
  exact a.trans ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective)

include d h hTH hp e in
/-- Faithfulness forces the plane endpoint on the left even before the
original outer extension has been bounded. -/
theorem original_unitaryFour_orientation : point = false := by
  cases point
  · rfl
  · have hmgt := d.original_unitaryFour_nonbinary h hTH hp m hm true e
    let a := (d.originalUnitaryFourLeftEquiv h hTH hp m hm true e).trans
      (MulEquiv.subgroupCongr (PointLocal.pointParabolic_solvableResidual m hm hmgt))
    exact (faithful_not_core_center_central h.local_mem.2 a
      (OriginalUnitaryFour.point_core_center_central m hm)).elim

omit point e in
include d h hTH hp in
/-- Both original residuals are the concrete plane and point factors, and
the left binary exponent is twice the unitary exponent. -/
theorem original_unitaryFour_factors
    (point : Bool) (e : OriginalUnitaryFour.Marking m hm point L R (sourceS L H)) :
    n = 2*m ∧ Nonempty (L ≃* L2 m hm) ∧
      Nonempty (R ≃* PointLocal.ProjectiveLocal m hm) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^m) := by
  have ho := d.original_unitaryFour_orientation h hTH hp m hm point e
  subst point
  have hmgt := d.original_unitaryFour_nonbinary h hTH hp m hm false e
  let a := (d.originalUnitaryFourLeftEquiv h hTH hp m hm false e).trans
    (MulEquiv.subgroupCongr (OriginalUnitaryFour.plane_parabolic_residual m hm))
  let b := (d.originalUnitaryFourRightEquiv h hTH hp m hm false e).trans
    (MulEquiv.subgroupCongr (PointLocal.pointParabolic_solvableResidual m hm hmgt))
  let aq := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    ((L2QuotientEquivSL2 m hm).trans
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := Representation.OrthogonalFourMinus.FiniteModel.Field m)))
  have hn : n = 2*m := by
    obtain ⟨F,_,_,hF,⟨f⟩⟩ := h.linear
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hc := binary_psl_field_card_eq (f.symm.trans aq)
    rw [hF,GaloisField.card 2 (2*m) (by omega)] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  refine ⟨hn,⟨a⟩,⟨b⟩,PointLocal.FixedField m,inferInstance,inferInstance,
    PointLocal.fixedField_card m hm,?_⟩
  exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
    (PointLocal.projectiveQuotientByTwoCoreEquivPSL m hm)⟩

include d h hTH hp e in
/-- The normalized original right Borel confines the whole outer part of S
to the actual join-core O₂(RS). The common inner Sylow is unchanged. -/
theorem original_unitaryFour_source_factorization :
    sourceS L H = (R ⊔ sourceS L H).pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ L) := by
  obtain ⟨_,_,_,F,_,_,hF,⟨f⟩⟩ := d.original_unitaryFour_factors h hTH hp m hm point e
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hs := (d.hypothesisF11 h hTH).linear_local_sylow_factorization 1 F f
    d.right_borel_normalizes_sourceS
  change sourceS L H = (R ⊔ sourceS L H).pCoreIn 2 ⊔ (sourceS L H ⊓ R) at hs
  rw [←d.original_unitaryFour_intersections h hTH hp m hm point e,d.left_intersection] at hs
  exact hs

include d h hTH hp e in
/-- The join-core meets the common inner Sylow in exactly the selected
right two-core. This is relative normality in RS. -/
theorem original_unitaryFour_join_core_intersection :
    ((T : Subgroup G) ⊓ L) ⊓ (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 := by
  have hs : (T : Subgroup G) ⊓ L = sourceS L H ⊓ R :=
    d.left_intersection.symm.trans (d.original_unitaryFour_intersections h hTH hp m hm point e)
  apply le_antisymm
  · exact (inf_le_inf (hs.le.trans inf_le_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 le_sup_left)
  · obtain ⟨P,hP⟩ := d.sylow 1
    have hcore : R.pCoreIn 2 ≤ sourceS L H ⊓ R := (pCoreIn_le_sylow R P).trans_eq hP
    exact le_inf (hcore.trans_eq hs.symm)
      (pCoreIn_mono_of_normalizes le_sup_left (sup_le R.le_normalizer d.S_normalizes_right))

include d h hTH hp e in
/-- The outer size of the original S is exactly the enlargement of the
right local core, before proving the degree-two bound. -/
theorem original_unitaryFour_outer_index :
    ((T : Subgroup G) ⊓ L).relIndex (sourceS L H) =
      (R.pCoreIn 2).relIndex ((R ⊔ sourceS L H).pCoreIn 2) := by
  have hs : (T : Subgroup G) ⊓ L ≤ sourceS L H :=
    d.left_intersection.symm ▸ inf_le_left
  have hn : (T : Subgroup G) ⊓ L ≤ normalizer ((R ⊔ sourceS L H).pCoreIn 2 : Set G) :=
    ((hs.trans le_sup_right).trans (R ⊔ sourceS L H).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image (R ⊔ sourceS L H) (pCore 2 (R ⊔ sourceS L H : Subgroup G)))
  conv_lhs => rw [d.original_unitaryFour_source_factorization h hTH hp m hm point e]
  rw [relIndex_sup_of_normalizes _ _ hn,←inf_relIndex_right,
    d.original_unitaryFour_join_core_intersection h hTH hp m hm point e]

include d h hTH hp e in
/-- The original join-core has q⁵ times the actual outer Sylow index.
No bound or parity conclusion is inserted into this count. -/
theorem original_unitaryFour_join_core_card :
    Nat.card ((R ⊔ sourceS L H).pCoreIn 2) =
      (2^m)^5 * ((T : Subgroup G) ⊓ L).relIndex (sourceS L H) := by
  obtain ⟨_,_,⟨b⟩,_⟩ := d.original_unitaryFour_factors h hTH hp m hm point e
  let bc := (b.subgroupMap (pCore 2 R)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 b))
  have hc : Nat.card (R.pCoreIn 2) = (2^m)^5 := by
    change Nat.card ((pCore 2 R).map R.subtype) = _
    rw [card_map_of_injective R.subtype_injective]
    exact (Nat.card_congr bc.toEquiv).trans (PointLocal.projectiveTwoCore_card m hm)
  have hle : R.pCoreIn 2 ≤ (R ⊔ sourceS L H).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le R.le_normalizer d.S_normalizes_right)
  have hh := ((R.pCoreIn 2).subgroupOf ((R ⊔ sourceS L H).pCoreIn 2)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,hc] at hh
  change (2^m)^5 * (R.pCoreIn 2).relIndex ((R ⊔ sourceS L H).pCoreIn 2) = _ at hh
  rw [←d.original_unitaryFour_outer_index h hTH hp m hm point e] at hh
  exact hh.symm


end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
