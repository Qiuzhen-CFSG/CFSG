module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableLocalExclusion

/-!
# Solvable subgroups normalized by the point parabolic

The literal point parabolic L₁T is solvable, since its two-core quotient
is S₃. A solvable subgroup N of the point normalizer normalized by L₁T
therefore generates a solvable overgroup with L₁T. Source 14.7.29 places
that overgroup in M = N_G(L), and characteristic two-residual transport
shows that N normalizes the original L₁.

Apply this to normal solvable subgroups of any original local, including
its full solvable radical. The normalization formulation is also the
containment used for component Borels in 14.7.32–33. It does not assert
the odd-core equality or identify any component model.

Source: Aschbacher–Smith, 14.7.29 and the Borel reduction in 14.7.32,
printed pp.1055–1056, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem point_parabolic_solvable
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Group.IsSolvable (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) := by
  let B : Subgroup G := F.Li L 1 ⊔ (T : Subgroup G)
  let : Group.IsNilpotent (pCore 2 B) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let : Group.IsSolvable (B ⧸ pCore 2 B) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (pointQuotientEquiv (F := F) h structural).toMonoidHom)
      (pointQuotientEquiv (F := F) h structural).injective
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 B)).mpr ⟨inferInstance,inferInstance⟩

/-- Every solvable subgroup of the point normalizer normalized by L₁T
lies in M. This is the source containment used for component Borels. -/
theorem point_normalized_solvable_le_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (N : Subgroup G) (hNH : N ≤ F.H) (hs : Group.IsSolvable N)
    (hn : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (N : Set G)) :
    N ≤ normalizer (L : Set G) := by
  let B : Subgroup G := F.Li L 1 ⊔ (T : Subgroup G)
  let := hs
  let : Group.IsSolvable B := point_parabolic_solvable h structural
  have hBH : B ≤ F.H := sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  exact le_sup_left.trans (solvable_point_overgroup_le_normalizer d h hab structural previous
    faithful earlier (N ⊔ B) (sup_le hNH hBH) le_sup_right
      (Group.isSolvable_sup_of_normalizes N B hn))

/-- The same actual subgroup normalizes the original point residual.
The normality statement concerns the literal L₁, before any quotient. -/
theorem point_normalized_solvable_normalizes_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (N : Subgroup G) (hNH : N ≤ F.H) (hs : Group.IsSolvable N)
    (hn : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (N : Set G)) :
    N ≤ normalizer (F.Li L 1 : Set G) := by
  have hNM := point_normalized_solvable_le_normalizer d h hab structural previous faithful earlier
    N hNH hs hn
  have hh := ((le_inf hNM (hNH.trans F.H.le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (L ⊓ F.H)
        (pResidual 2 (L ⊓ F.H : Subgroup G)))
  have he : F.Li L 1 = (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype := by
    simp only [InvariantFlag.Li,show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,if_false]
    rfl
  rwa [he]

/-- Solvable normal subgroups of arbitrary original locals lie in M. -/
theorem local_normal_solvable_le_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (N : Subgroup I) [N.Normal] (hs : Group.IsSolvable N) :
    N.map I.subtype ≤ normalizer (L : Set G) := by
  have hIN : I ≤ normalizer (N.map I.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      N.le_normalizer_map I.subtype
  let := hs
  exact point_normalized_solvable_le_normalizer d h hab structural previous faithful earlier
    (N.map I.subtype) ((map_subtype_le N).trans hI.2.1)
    (Group.isSolvable_of_surjective (f := I.subtype.subgroupMap N)
      (I.subtype.subgroupMap_surjective N))
    ((sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)).trans hIN)

/-- The actual solvable radical, including every normal three-core lift,
is contained in the original normalizer. -/
theorem local_solvableRadical_le_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    (solvableRadical I).map I.subtype ≤ normalizer (L : Set G) :=
  local_normal_solvable_le_normalizer d h hab structural previous faithful earlier I hI
    (solvableRadical I) inferInstance

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
