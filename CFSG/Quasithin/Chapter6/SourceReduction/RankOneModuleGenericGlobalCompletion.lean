module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobal
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PGroup.CharacteristicKernel
public import Theory.GroupTheory.SolvableResidual.NormalSupplement

/-!
# Cores and residuals in the actual generic completion

Write K = O²(H), S = O₂(N_G(L) ∩ H), G₀ = ⟨L,K,S⟩ and X = ⟨L,H⟩.
The source Sylow T normalizes both K and S. Thus KS is normal in H = KT;
since O₂(H) lies in S, this proves O₂(KT) = O₂(KS) without amalgam
classification. This is the final core equality in 5.2.6.

The same normalization gives G₀ normal in X and G₀T = X. When L and K
are perfect, both G₀ and X have solvable residual exactly ⟨L,K⟩. Original
uniqueness over L and escape of K also give O₂(X) = 1. These statements
keep the possible two-group extension separate from its perfect residual;
they do not identify X with the ambient group or recognize a completion.

The Chapter12 consumer applies this to the original prepared pair. Its
exhaustive comparison and uniqueness inputs remain explicit, and the
Green Book classification and ambient recognition remain unproved here.
Source: Aschbacher–Smith 5.2.5–7, printed pp.650–651, and the transition
to completion recognition on p.652 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H : Subgroup G}

omit [Finite G] in
/-- The original T acts on the intersection core S; no equality S = T is used. -/
theorem sylow_normalizes_sourceS
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    (T : Subgroup G) ≤ normalizer (sourceS L H : Set G) :=
  (le_inf hTL hTH).trans (intersection_normalizes_sourceS L H)

/-- The source subgroup KS is normal in H = KT, rather than in the ambient group. -/
theorem residual_sourceS_normalized
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    H ≤ normalizer ((residual H ⊔ sourceS L H : Subgroup G) : Set G) := by
  have hT := (le_inf (hTH.trans (le_normalizer_residual H))
    (sylow_normalizes_sourceS hTL hTH)).trans
      (normalizer_inf_normalizer_le_normalizer_sup (residual H) (sourceS L H))
  calc
    H = residual H ⊔ (T : Subgroup G) := (residual_sup_sylow T H hTH).symm
    _ ≤ _ := sup_le (le_sup_left.trans (residual H ⊔ sourceS L H).le_normalizer) hT

/-- The actual H and KS have the same embedded two-core. -/
theorem residual_sourceS_core_eq
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    (residual H ⊔ sourceS L H).pCoreIn 2 = H.pCoreIn 2 := by
  have hSH : sourceS L H ≤ H := (map_subtype_le _).trans inf_le_right
  have hJH : residual H ⊔ sourceS L H ≤ H := sup_le (map_subtype_le _) hSH
  apply le_antisymm
  · exact pCoreIn_mono_of_normalizes hJH (residual_sourceS_normalized hTL hTH)
  · have hcore : H.pCoreIn 2 ≤ sourceS L H :=
      Chapter3.twoCore_le_of_sylow_le T (le_inf hTL hTH) inf_le_right
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
      (hcore.trans le_sup_right)
      (hJH.trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))

/-- The literal core identity at the end of source 5.2.6. -/
theorem residual_sylow_core_eq_sourceS
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    (residual H ⊔ (T : Subgroup G)).pCoreIn 2 =
      (residual H ⊔ sourceS L H).pCoreIn 2 := by
  rw [residual_sup_sylow T H hTH]
  exact (residual_sourceS_core_eq hTL hTH).symm

omit [Finite G] in
/-- The whole ambient Sylow normalizes the local completion with right factor K. -/
theorem residual_completion_sylow_normalizes
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    (T : Subgroup G) ≤ normalizer
      (ChapterF.Source.generated ![L,residual H] (sourceS L H) : Set G) := by
  have hLK := (le_inf hTL (hTH.trans (le_normalizer_residual H))).trans
    (normalizer_inf_normalizer_le_normalizer_sup L (residual H))
  exact (le_inf hLK (sylow_normalizes_sourceS hTL hTH)).trans
    (normalizer_inf_normalizer_le_normalizer_sup (L ⊔ residual H) (sourceS L H))

/-- Adjoining T to the source completion gives exactly the join of L and H. -/
theorem residual_completion_sup_sylow
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    ChapterF.Source.generated ![L,residual H] (sourceS L H) ⊔ (T : Subgroup G) =
      L ⊔ H := by
  change L ⊔ residual H ⊔ sourceS L H ⊔ (T : Subgroup G) = _
  rw [sup_assoc, sup_eq_right.mpr (sourceS_le_sylow hTL hTH), sup_assoc,
    residual_sup_sylow T H hTH]

/-- Normality of the source completion is relative to the actual join of L and H. -/
theorem residual_completion_normal_in_pair
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    ((ChapterF.Source.generated ![L,residual H] (sourceS L H)).subgroupOf (L ⊔ H)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [← residual_completion_sup_sylow hTL hTH]
  exact sup_le (ChapterF.Source.generated ![L,residual H] (sourceS L H)).le_normalizer
    (residual_completion_sylow_normalizes hTL hTH)

/-- The solvable residual of the Sylow-enlarged completion is precisely the join of its perfect factors. -/
theorem residual_pair_solvableResidual
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    (hpL : Group.IsPerfect L) (hpK : Group.IsPerfect (residual H)) :
    (solvableResidual (L ⊔ H : Subgroup G)).map (L ⊔ H).subtype = L ⊔ residual H := by
  let := hpL
  let := hpK
  let X := L ⊔ H
  let J := L ⊔ residual H
  have hJX : J ≤ X := sup_le le_sup_left ((map_subtype_le _).trans le_sup_right)
  have hTX : (T : Subgroup G) ≤ X := hTH.trans le_sup_right
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (le_inf hTL (hTH.trans (le_normalizer_residual H))).trans
      (normalizer_inf_normalizer_le_normalizer_sup L (residual H))
  have hgen : J ⊔ (T : Subgroup G) = X := by
    dsimp only [J, X]
    rw [sup_assoc, residual_sup_sylow T H hTH]
  let N := J.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (show X ≤ normalizer (J : Set G) from hgen ▸ sup_le J.le_normalizer hTJ)
  have hq : IsPGroup 2 (X ⧸ N) := by
    apply quotient_isPGroup_of_sup_eq_top ((T : Subgroup G).subgroupOf X) N
      T.isPGroup'.comap_subtype
    rw [← subgroupOf_sup hTX hJX, sup_comm, hgen, subgroupOf_self]
  let : Group.IsNilpotent (X ⧸ N) := hq.isNilpotent
  let : Group.IsSolvable (X ⧸ N) := inferInstance
  apply le_antisymm
  · have he := map_mono (f := X.subtype) (solvableResidual_le_of_solvable_quotient N)
    rwa [map_subgroupOf_eq_of_le hJX] at he
  · exact sup_le (le_map_solvableResidual_of_isPerfect L X le_sup_left)
      (le_map_solvableResidual_of_isPerfect (residual H) X
        ((map_subtype_le _).trans le_sup_right))

/-- Original uniqueness over L also kills the two-core after adjoining the full T. -/
theorem Preparation.residual_pair_twoCore_eq_bot {A B : Subgroup G}
    (d : Preparation T L H A B (residual H)) : pCore 2 (L ⊔ H : Subgroup G) = ⊥ := by
  by_contra hc
  obtain ⟨X,hX,hgen⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot (L ⊔ H) hc
  have he := d.unique_left X hX (le_sup_left.trans hgen)
  exact d.right_outside (he ▸ ((map_subtype_le _).trans le_sup_right).trans hgen)

/-- The original local completion and its Sylow enlargement have the same perfect residual. -/
theorem residual_completion_solvableResidual
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    (hpL : Group.IsPerfect L) (hpK : Group.IsPerfect (residual H)) :
    (solvableResidual (ChapterF.Source.generated ![L,residual H] (sourceS L H))).map
      (ChapterF.Source.generated ![L,residual H] (sourceS L H)).subtype = L ⊔ residual H := by
  have hp : Group.IsPerfect ((solvableResidual (L ⊔ H : Subgroup G)).map (L ⊔ H).subtype) :=
    Group.IsPerfect.map (L ⊔ H).subtype
  rw [residual_pair_solvableResidual hTL hTH hpL hpK] at hp
  let := hp
  have hS : IsPGroup 2 (sourceS L H) := pCore_isPGroup.map _
  let : Group.IsNilpotent (sourceS L H) := hS.isNilpotent
  let : Group.IsSolvable (sourceS L H) := inferInstance
  have hn := (le_inf hTL (hTH.trans (le_normalizer_residual H))).trans
    (normalizer_inf_normalizer_le_normalizer_sup L (residual H))
  exact map_solvableResidual_sup_eq_of_perfect_normalized (L ⊔ residual H)
    (sourceS L H) ((sourceS_le_sylow hTL hTH).trans hn)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
