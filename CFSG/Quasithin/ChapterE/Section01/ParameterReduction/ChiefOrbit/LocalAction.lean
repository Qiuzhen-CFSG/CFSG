module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Action
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.Families
public import Theory.GroupTheory.GeneralizedFitting.ChiefComponents
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Local generation from a chief component's actual action

Subnormal Sylow intersection and the normalized-product index formula show that
`N_T(J)` is Sylow in `JS`, with precisely the ambient intersection `T ∩ JS`.
Chief minimality makes J centerless, so its two-core is trivial and the existing
core-quotient action theorem applies to the literal conjugation image. This
proves local generation and closes the case where the chief residual itself is
a component. Permuted components require the two separate diagonal branches.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed pp.212--214.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The local product meets the supplied Sylow subgroup in its stabilizer. -/
theorem inf_localGroup (T : Sylow 2 G) (J : Subgroup G) :
    (T : Subgroup G) ⊓ localGroup T J = stabilizer T J := by
  apply le_antisymm
  · exact inf_le_inf le_rfl (sup_le J.le_normalizer inf_le_right)
  · exact le_inf inf_le_left le_sup_right

/-- Subnormality of the component suffices for the literal local Sylow intersection. -/
theorem exists_localSylow (T : Sylow 2 G) (J : Subgroup G) (hJ : J.IsSubnormal) :
    ∃ R : Sylow 2 (localGroup T J),
      (R : Subgroup (localGroup T J)) = (stabilizer T J).subgroupOf (localGroup T J) := by
  obtain ⟨D, hD⟩ := T.exists_subgroupOf_eq_of_subnormal J hJ
  have hDS : (D : Subgroup J).map J.subtype ≤ stabilizer T J := by
    rw [hD, subgroupOf_map_subtype]
    exact le_inf inf_le_left (inf_le_right.trans J.le_normalizer)
  obtain ⟨R, hR⟩ := IsPGroup.exists_sylow_sup_of_coprime_index J (stabilizer T J)
    (T.isPGroup'.to_le inf_le_left) inf_le_right (D : Subgroup J) D.not_dvd_index hDS
  refine ⟨R, ?_⟩
  apply map_injective (localGroup T J).subtype_injective
  exact hR.trans (map_subgroupOf_eq_of_le (show stabilizer T J ≤ localGroup T J from
    le_sup_right)).symm

/-- Chief minimality makes the component centerless, and hence kills its two-core.
The centerless quotient needed by the actual action theorem is a conclusion. -/
theorem component_coreQuotient_center_eq_bot {X J : Subgroup G}
    (hX : ChiefFactor.IsChief X ⊥) (hna : ¬ IsMulCommutative X)
    (hJ : IsComponentIn J X) : center (J ⧸ pCore 2 J) = ⊥ := by
  let _ := hJ.quasisimple
  have hz := hX.component_center_eq_bot hna hJ
  have hc : pCore 2 J = ⊥ := bot_unique ((IsQuasisimple.pCore_le_center 2).trans hz.le)
  let e : J ⧸ pCore 2 J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  apply eq_bot_iff.mpr
  intro j hj
  have he : e j ∈ center J := (centerCongr e ⟨j, hj⟩).property
  rw [hz, mem_bot] at he
  exact mem_bot.mpr (e.injective (he.trans e.map_one.symm))

/-- The precise component-action premise of E.1.11 gives generation of `JS`. -/
theorem local_isEGenerated {n : ℕ} (T : Sylow 2 G) {X J : Subgroup G}
    (hX : ChiefFactor.IsChief X ⊥) (hna : ¬ IsMulCommutative X)
    (hJ : IsComponentIn J X)
    (hgen : IsEGenerated n
      (pCoreJoinAction 2 (show stabilizer T J ≤ normalizer J from inf_le_right)).range) :
    IsEGenerated n (localGroup T J) :=
  isEGenerated_join_of_pCoreJoinAction J (stabilizer T J) inf_le_right
    (T.isPGroup'.to_le inf_le_left) (component_coreQuotient_center_eq_bot hX hna hJ) hgen

/-- For a component fixed by the Sylow subgroup, the chief residual case closes
without an orbit-diagonal argument. -/
theorem isEGenerated_of_residual_component {n : ℕ} (T : Sylow 2 G)
    (hX : ChiefFactor.IsChief (pResidual 2 G) ⊥)
    (hna : ¬ IsMulCommutative (pResidual 2 G))
    (hJ : IsComponentIn (pResidual 2 G) (pResidual 2 G))
    (hgen : IsEGenerated n
      (pCoreJoinAction 2 (show stabilizer T (pResidual 2 G) ≤ normalizer (pResidual 2 G)
        from inf_le_right)).range) : IsEGenerated n G := by
  have hg := local_isEGenerated T hX hna hJ hgen
  have he : localGroup T (pResidual 2 G) = ⊤ := by
    simp only [localGroup, stabilizer, normalizer_eq_top, inf_top_eq]
    exact pResidual_sup_sylow_eq_top T
  exact hg.map_equiv ((MulEquiv.subgroupCongr he).trans topEquiv)

end CFSG.Quasithin.ChapterE.ChiefOrbit
