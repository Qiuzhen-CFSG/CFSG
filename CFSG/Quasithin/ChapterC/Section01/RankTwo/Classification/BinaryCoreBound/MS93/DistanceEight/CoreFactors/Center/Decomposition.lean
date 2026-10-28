module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.NaturalPair
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The residual fixed factor is the remaining center input

The completed reverse-center argument identifies the core center with
core intersected with Z. The original natural splitting of Z then splits
that center as U times the residual fixed factor. Thus its order is eight
times the order of that exact fixed factor. The result is transported back
through the original embedM map, and the whole center is elementary abelian.

Identifying the fixed factor with H remains the final source collection
obligation in (4.5)(iii)--(iv); no such equality or bound is assumed here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5), printed p.895.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

theorem core_center_le_Z_of_earlier (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    (center (core R (alpha R))).map (core R (alpha R)).subtype ≤ Z R (alpha R) := by
  obtain ⟨p⟩ := Early.sourcePath_nonempty source common earlier (alpha R) rfl
  exact core_center_le_Z common earlier p

theorem core_center_eq_inf_Z (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    (center (core R (alpha R))).map (core R (alpha R)).subtype =
      core R (alpha R) ⊓ Z R (alpha R) := by
  apply le_antisymm (le_inf (map_subtype_le _) (core_center_le_Z_of_earlier common earlier))
  rintro x ⟨hx,hz⟩
  refine ⟨⟨x,hx⟩,mem_center_iff.mpr ?_,rfl⟩
  intro y
  exact Subtype.ext (Higher.Quotients.FirstDirect.Z_centralizes_core common earlier hz y y.property)

theorem core_fixedFactor_le_Z (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    core R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) ≤ Z R (alpha R) :=
  (fixedFactor_le_coreCenter _).trans (core_center_le_Z_of_earlier common earlier)

theorem core_center_eq_U_sup_fixedFactor (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    (center (core R (alpha R))).map (core R (alpha R)).subtype =
      U R (alpha R) ⊔ (core R (alpha R) ⊓
        centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))) := by
  let K := core R (alpha R)
  let F := Z R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))
  have hUK : U R (alpha R) ≤ K :=
    DistanceTwo.U_le_core geometry (by have := common.large_distance; omega) _ rfl
  have hn : U R (alpha R) ≤ normalizer F :=
    (le_centralizer_iff.mp (inf_le_left.trans
      ((Higher.Quotients.FirstDirect.Z_centralizes_core common earlier).trans
        (centralizer_le hUK)))).trans (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm ?_ (sup_le (le_sup_left.trans (earlier.factor_inclusions common).2.1)
    (fixedFactor_le_coreCenter _))
  intro x hx
  have hz := core_center_le_Z_of_earlier common earlier hx
  have hprod : x ∈ (U R (alpha R) : Set (FreeAmalgam R)) * (F : Set (FreeAmalgam R)) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hn]
    exact common.decomposition ▸ hz
  obtain ⟨u,hu,f,hf,huf⟩ := hprod
  have hfK : f ∈ K := by
    have h := K.mul_mem (K.inv_mem (hUK hu)) ((map_subtype_le _) hx)
    rw [← huf,inv_mul_cancel_left] at h
    exact h
  rw [← huf]
  exact mul_mem (mem_sup_left hu) (mem_sup_right ⟨hfK,hf.2⟩)

theorem U_disjoint_core_fixedFactor (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    Disjoint (U R (alpha R)) (core R (alpha R) ⊓
      centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))) :=
  common.disjoint.mono_right (le_inf (core_fixedFactor_le_Z common earlier) inf_le_right)

theorem core_center_card_eq_eight_mul_fixedFactor (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    Nat.card (center (core R (alpha R))) = 8 * Nat.card (core R (alpha R) ⊓
      centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) : Subgroup (FreeAmalgam R)) := by
  let K := core R (alpha R)
  let D := K ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))
  have hDU : D ≤ centralizer (U R (alpha R) : Set (FreeAmalgam R)) :=
    (core_fixedFactor_le_Z common earlier).trans
      ((Higher.Quotients.FirstDirect.Z_centralizes_core common earlier).trans
        (centralizer_le (DistanceTwo.U_le_core geometry
          (by have := common.large_distance; omega) _ rfl)))
  rw [Nat.card_congr ((center K).equivMapOfInjective K.subtype K.subtype_injective).toEquiv,
    core_center_eq_U_sup_fixedFactor common earlier,
    card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (hDU.trans (Subgroup.centralizer_le_normalizer _)) (U_disjoint_core_fixedFactor common earlier),
    U_card R common.natural]
theorem core_center_elementary (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) : IsElementaryAbelian 2 (center (core R (alpha R))) := by
  have hZ : Z R (alpha R) = omegaCenter (Q R (alpha R)) :=
    (common.X_eq_Z (alpha R) rfl).symm
  let : IsElementaryAbelian 2 (Z R (alpha R)) := by
    rw [hZ]
    exact omegaCenter_elementary _
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Z R (alpha R)) _
    (core_center_le_Z_of_earlier common earlier (mem_map_of_mem _ x.property))

/-- Literal transport back through the original amalgam embedding. -/
theorem reduced_core_center_card_eq_eight_mul_fixedFactor (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    Nat.card (center (commutatorCore L)) = 8 * Nat.card (core R (alpha R) ⊓
      centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) : Subgroup (FreeAmalgam R)) := by
  let e : commutatorCore L ≃* core R (alpha R) :=
    ((commutatorCore L).equivMapOfInjective (embedM R) (embedM_injective R)).trans
      (MulEquiv.subgroupCongr (core_alpha R source.two_group source.core_le source.residual).symm)
  rw [Nat.card_congr (centerCongr e).toEquiv]
  exact core_center_card_eq_eight_mul_fixedFactor common earlier

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
