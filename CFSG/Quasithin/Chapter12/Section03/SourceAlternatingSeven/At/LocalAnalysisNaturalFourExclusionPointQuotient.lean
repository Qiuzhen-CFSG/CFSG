module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionPointQuotient
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionControl
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNormalizer

/-!
# LocalAnalysisNaturalFourExclusionPointQuotient at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalFourExclusionPointQuotient`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

private theorem component_point_comap_at
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (z : V) :
    (L ⊓ centralizer ({(z : G)} : Set G)).subgroupOf L =
      (BinaryAlternatingSevenControl.pointStabilizer
        (S.fourFaithfulAction e) (S.fourPointVector z)).comap (S.fourFaithfulProjection e) := by
  let := S.chosen.actionCentralizer_normal
  ext l
  change ((l : G) ∈ L ∧ (l : G) ∈ centralizer ({(z : G)} : Set G)) ↔ _
  rw [and_iff_right l.property, mem_comap, BinaryAlternatingSevenControl.mem_pointStabilizer]
  have he : S.fourFaithfulAction e (S.fourFaithfulProjection e l) =
      S.chosen.chosenAction l := by
    change S.chosen.faithfulAction (e.symm (e (QuotientGroup.mk' _ l))) = _
    rw [e.symm_apply_apply]
    rfl
  rw [he]
  have hi : Function.Injective (fun w : S.chosen.space =>
      (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) :=
    Subtype.val_injective.comp (S.chosen.spaceEquiv.injective.comp Multiplicative.ofAdd.injective)
  rw [← hi.eq_iff]
  have hv : (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.fourPointVector z)) : G) = z :=
    congrArg Subtype.val (S.chosen.spaceEquiv.apply_symm_apply z)
  have ha : (S.chosen.spaceEquiv (Multiplicative.ofAdd
      (S.chosen.chosenAction l (S.fourPointVector z))) : G) =
      (l : G) * (z : G) * (l : G)⁻¹ := by
    rw [S.chosen.spaceEquiv_apply]
    change (l : G) * _ * (l : G)⁻¹ = _
    congr 1
    congr 1
    exact (S.chosen.spaceEquiv_apply (S.fourPointVector z)).symm.trans hv
  rw [ha,hv,mem_centralizer_singleton_iff,mul_inv_eq_iff_eq_mul]

private theorem vector_nonzero_at {z : V} (hz : z ≠ 1) : S.fourPointVector z ≠ 0 := by
  intro he
  apply hz
  have h := congrArg (fun w => S.chosen.spaceEquiv (Multiplicative.ofAdd w)) he
  simpa only [fourPointVector, ofAdd_toAdd, MulEquiv.apply_symm_apply, ofAdd_zero, map_one] using h

theorem fourResidualData_of_pointPerfect_le_component_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (hKL : S.fourPointPerfect z ≤ L) : S.FourResidualData z := by
  apply S.fourResidualData_of_quotient_at structural e hd hz hz1 hzT
  rw [S.four_pointPerfect_eq_componentPointPerfect_of_le hKL]
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨S.fourComponentPointCoreEquiv e hd ⟨z,hz⟩
      (fun he => hz1 (congrArg Subtype.val he))⟩⟩

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

