module
public import Theory.GroupTheory.PResidual.IndexThreeCommutator
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Sylow

/-!
# The original residual and near-maximum Thompson actor

Restrict the actual common Sylow to B and transport its J₁ through the
injective subtype map. The index-three commutator criterion then identifies
exactly what remains to prove the source identity O²(B)=[O²(B),J₁(T)]:
J₁(T) must escape O₂(B). Residual movement also excludes J₁-normality in
any overgroup containing the same B, the contradiction used for case (iv).

These are reductions with the full original residual. They do not establish
the escape or the trichotomy that supplies it in source 13.4.7(4).
Source: Aschbacher–Smith 13.4.7(4), printed pp.902–903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
variable {G : Type*} [Group G] [Finite G]

/-- The exact original residual commutator, characterized by J₁'s escape
from the local two-core. Neither residual is replaced by a two-core. -/
theorem original_residual_thompson_one_iff
    {T : Sylow 2 G} {B : Subgroup G} (hTB : (T : Subgroup G) ≤ B)
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) :
    ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
      (pResidual 2 B).map B.subtype ↔
      ¬ ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2 := by
  let S := T.subtype hTB
  let R := ChapterB.thompsonJ (S : Subgroup B) 1
  have hm : R.map B.subtype = ChapterB.thompsonJ (T : Subgroup G) 1 := by
    rw [←ChapterB.thompsonJ_map_injective B.subtype B.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTB]
  have he := residual_commutator_iff_of_index_three S
    (SymmetricThreeTwoCore.sylow_index_three eB S) R
    (ChapterB.thompsonJ_le _ _) (ChapterB.le_normalizer_thompsonJ _ _)
  constructor
  · intro hh hle
    apply he.mp ?_ ((map_le_map_iff_of_injective B.subtype_injective).mp ?_)
    · apply map_injective B.subtype_injective
      rwa [map_commutator,hm]
    · simpa only [hm,pCoreIn] using hle
  · intro hh
    have hr : ¬ R ≤ pCore 2 B := by
      intro hle
      apply hh
      rw [←hm]
      exact map_mono hle
    have hcomm := congrArg (Subgroup.map B.subtype) (he.mpr hr)
    simpa only [map_commutator,hm] using hcomm
/-- The original residual movement rules out J₁-normality in every
overgroup of the same second parabolic, as required to exclude 13.4.7(iv). -/
theorem not_thompson_one_normalizer_of_residual_movement
    {T : Sylow 2 G} {B X : Subgroup G} (hTB : (T : Subgroup G) ≤ B)
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hBX : B ≤ X)
    (hmove : ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
      (pResidual 2 B).map B.subtype) :
    ¬ X ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
  intro hn
  apply (original_residual_thompson_one_iff hTB eB).mp hmove
  exact le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le (ChapterB.thompsonJ_le _ _))
    ((ChapterB.thompsonJ_le _ _).trans hTB) (hBX.trans hn)

/-- Lift the source's barred residual movement through its actual map.
The index-three hypothesis avoids assuming that the full kernel is a two-group. -/
theorem original_residual_thompson_one_of_image
    {F : Type*} [Group F]
    {T : Sylow 2 G} {B : Subgroup G} (hTB : (T : Subgroup G) ≤ B)
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (f : B →* F) (hne : (pResidual 2 B).map f ≠ ⊥)
    (hmove : ⁅(pResidual 2 B).map f,
      ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf B).map f⁆ =
        (pResidual 2 B).map f) :
    ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
      (pResidual 2 B).map B.subtype := by
  let S := T.subtype hTB
  let R := ChapterB.thompsonJ (S : Subgroup B) 1
  have hm : R.map B.subtype = ChapterB.thompsonJ (T : Subgroup G) 1 := by
    rw [←ChapterB.thompsonJ_map_injective B.subtype B.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTB]
  have hr : (ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf B = R := by
    rw [←hm,subgroupOf,comap_map_eq_self_of_injective B.subtype_injective]
  rw [hr] at hmove
  have hc := residual_commutator_of_nontrivial_image_of_index_three S
    (SymmetricThreeTwoCore.sylow_index_three eB S) R
    (ChapterB.thompsonJ_le _ _) (ChapterB.le_normalizer_thompsonJ _ _) f hne hmove
  have hh := congrArg (Subgroup.map B.subtype) hc
  simpa only [map_commutator,hm] using hh

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
