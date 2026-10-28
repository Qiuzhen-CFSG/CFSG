module
public import CFSG.Quasithin.Chapter14.Section02.UnitaryKOne
public import CFSG.Quasithin.Chapter14.Section02.SourceSetup

/-!
# The original normal-branch amalgam core in 14.2.15

For the original normal component K, its ambient Sylow normalizer S is T.
The source's S₂ = O₂(Y)(T intersection K) lies in T, because T normalizes
Y and hence its two-core. Therefore the literal F.1.1 generated group
for K, YS₂, S is precisely the already core-free join of H and YT.
This discharges 14.2.13 and 14.2.15 in the normal branch without a new
common-normal, placement, or classification premise. The crossed branch
and the other F.1.1 clauses are separate arguments.

Source: Aschbacher--Smith 14.2.8(1), 14.2.13--15, printed pp.983--985.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_normal_amalgam_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤) :
    let Y := sourceResidual M Mc
    let K₁ := K.map H.subtype
    let S := (T : Subgroup G) ⊓ normalizer (K₁ : Set G)
    let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K₁)
    S = (T : Subgroup G) ∧ Y.pCoreIn 2 ≤ S ∧ S₂ ≤ S ∧
      pCore 2 (ChapterF.Source.generated ![K₁,Y ⊔ S₂] S) = ⊥ := by
  let Y := sourceResidual M Mc
  let K₁ := K.map H.subtype
  let S := (T : Subgroup G) ⊓ normalizer (K₁ : Set G)
  let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K₁)
  have hHN : H ≤ normalizer (K₁ : Set G) := by
    have hh := K.le_normalizer_map H.subtype
    rwa [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at hh
  have hS : S = (T : Subgroup G) := inf_eq_left.mpr (hH.1.1.2.trans hHN)
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    hM.1.2.trans ((normal_subgroupOf_iff_le_normalizer (sourceResidual_le M Mc)).mp
      (residualY_normal M Mc))
  have hTQ := hTY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hQT : Y.pCoreIn 2 ≤ (T : Subgroup G) := by
    exact sup_eq_right.mp (T.is_maximal'
      ((isPGroup_pCoreIn 2 Y).to_sup_of_normal_left' T.isPGroup' hTQ) le_sup_right)
  have hS₂ : S₂ ≤ (T : Subgroup G) := sup_le hQT inf_le_left
  have hKT : K₁ ⊔ (T : Subgroup G) = H := by
    have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
    change K ⊔ (T.subtype hTH : Subgroup H) = ⊤ at hgen
    have hh := congrArg (Subgroup.map H.subtype) hgen
    simpa only [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
      ←MonoidHom.range_eq_map,range_subtype] using hh
  have hg : ChapterF.Source.generated ![K₁,Y ⊔ S₂] S = H ⊔ (Y ⊔ (T : Subgroup G)) := by
    change K₁ ⊔ (Y ⊔ S₂) ⊔ S = _
    rw [hS,←hKT]
    apply le_antisymm
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left)
        (sup_le (le_sup_left.trans le_sup_right) (hS₂.trans (le_sup_right.trans le_sup_right))))
        (le_sup_right.trans le_sup_right)
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (sup_le ((le_sup_left.trans le_sup_right).trans le_sup_left) le_sup_right)
  refine ⟨hS,hQT.trans hS.ge,hS₂.trans hS.ge,?_⟩
  rw [hg]
  exact source_solvable_amalgam_twoCore_eq_bot hG T hempty hM hu hmany hcard e H hH.1.2
end CFSG.Quasithin.Chapter14.Section02
