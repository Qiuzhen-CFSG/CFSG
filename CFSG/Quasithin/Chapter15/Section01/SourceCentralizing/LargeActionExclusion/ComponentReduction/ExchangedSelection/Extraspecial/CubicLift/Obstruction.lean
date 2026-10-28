module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.SourceSelection.Original
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.CubicLift
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.Thompson
/-!
# The exact central-preimage lift obstruction

The original Thompson image fixes the marked cubic plane pointwise, so it
centralizes the extraspecial center. That center therefore preserves V_E.
Its full preimage X₀ lies in N_G(V_E), which earlier 15.1.14 places in Mc.
Thus X₀ lies in M ∩ Mc and normalizes R = O₂(M ∩ Mc). Consequently
⟨R^{X₀}⟩ = R and its two-residual is trivial.

This is an obstruction to the intermediate cubic lift in the literal
sourceCentralLiftResidual, not a counterexample to the full extraspecial
exclusion: the ambient extraspecial hypotheses may themselves be impossible.
The original conditional lift APIs remain valid. Their center-movement
premise cannot be supplied alongside these earlier hypotheses without first
excluding the row. Final extraspecial exclusion and exchanged selection
remain with qt-e-1515-exchanged-component-selection and need another route.

Source comparison: Aschbacher--Smith 15.1.14(2), 15.1.16(c), and the proof
of 15.1.24(1), printed pp.1091,1092,1101. The rendered p.1101 defines X₀
using Z(O²(M̄)) and X₁ = O²(⟨R^{X₀}⟩); both conventions are retained here.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal residual-center preimage preserves the original Thompson fixed subgroup. -/
theorem ImageMarking.centralPreimage_normalizes_thompsonFixed
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hex : SourceCases.Extraspecial (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict))
    (c : ImageMarking T M V hn) :
    centralPreimage M V hn ≤ normalizer (thompsonFixed T V : Set G) := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f := (actionHom M V hn).rangeRestrict
  let P := pResidual 2 D
  let Z := (center P).map P.subtype
  let J := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let W := fixedSpace ρ J
  obtain ⟨_,_,_,hP,hcard,_,hdim,_⟩ := hex
  let := hP
  have hjk : J ≤ subspaceKernel ρ (fixedSpace ρ (c.X.map P.subtype)) ⊤ := by
    intro j hj
    exact ⟨mem_top _,fun v hv => c.fixed_thompson hv ⟨j,hj⟩⟩
  have hjz : J ≤ centralizer (Z : Set D) := hjk.trans
    (ExtraspecialBinarySix.noncentral_cubic_stabilizer_centralizes_center
      ρ (imageRepresentation_injective M V hn) P hcard hdim c.X c.card_X c.noncentral)
  have hnorm : Z ≤ subspaceStabilizer ρ W :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ Z J
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hjz))
  rw [←DecomposableMarker.plane_thompson_image hTM hn]
  apply le_normalizer_iff.mpr
  rintro x ⟨m,hm,rfl⟩ y ⟨v,hv,rfl⟩
  refine ⟨(actionHom M V hn m) v,?_,rfl⟩
  exact (hnorm hm (Additive.ofMul v)).mpr hv

omit [Finite G] in
private theorem sourceCentralLiftResidual_eq_bot_of_centralPreimage_le
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (hx : centralPreimage M V hn ≤ Mc) :
    sourceCentralLiftResidual M Mc V hn = ⊥ := by
  let R := (M ⊓ Mc).pCoreIn 2
  have hxM : centralPreimage M V hn ≤ M := map_subtype_le _
  have hnorm : centralPreimage M V hn ≤ normalizer (R : Set G) :=
    (le_inf hxM hx).trans ((M ⊓ Mc).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (M ⊓ Mc : Subgroup G))))
  have he : conjugateSpanBy R (centralPreimage M V hn) = R :=
    le_antisymm (conjugateSpanBy_le le_rfl hnorm) (le_conjugateSpanBy _ _)
  have hp : pResidual 2 R = ⊥ := by
    apply bot_unique
    simpa only [MonoidHom.ker_id] using
      (pResidual_le_ker_of_isPGroup 2 (MonoidHom.id R) (isPGroup_pCoreIn 2 (M ⊓ Mc)))
  change (pResidual 2 (conjugateSpanBy R (centralPreimage M V hn))).map _ = ⊥
  rw [he,hp,Subgroup.map_bot]

/-- Under the earlier normalizer conclusion, the prescribed exact lift residual is trivial. -/
theorem ImageMarking.sourceCentralLiftResidual_eq_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (c : letI := h.elementary; ImageMarking T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (thompsonFixed T V : Set G)) :
    letI := h.elementary; sourceCentralLiftResidual M Mc V h.normalized = ⊥ := by
  let := h.elementary
  apply sourceCentralLiftResidual_eq_bot_of_centralPreimage_le h.normalized
  exact (c.centralPreimage_normalizes_thompsonFixed T hM.1.2 h.normalized hex).trans
    (h.thompsonFixed_normalizers hG T hM hJ hu hres).2.1
end CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The source hypotheses and the constructed marking force the prescribed
central-preimage residual to be trivial. This obstructs that intermediate
lift target, not the final exclusion of the extraspecial row. -/
theorem PreparedChosenModule.source_extraspecial_centralLiftResidual_eq_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (thompsonFixed T V : Set G)) :
    letI := h.elementary; ExtraspecialMarker.sourceCentralLiftResidual M Mc V h.normalized = ⊥ := by
  let := h.elementary
  obtain ⟨c⟩ := h.extraspecial_imageMarking hG T hempty hM hmany hJ hfull hex
  exact c.sourceCentralLiftResidual_eq_bot hG T hM hJ hu h hex hres

end CFSG.Quasithin.Chapter15.Section01