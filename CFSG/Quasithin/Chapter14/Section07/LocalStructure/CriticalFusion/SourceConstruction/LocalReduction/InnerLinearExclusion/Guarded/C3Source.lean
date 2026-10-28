module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.C3Source
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.LinearSource

/-!
# Original small-quotient exclusion: C3Source

The source proof is specialized to the same G,T structural and escape inputs.
All subgroup restrictions, quotient maps and the actual rank-three system
are retained. The universal public API in the original module is unchanged.
Source: Aschbacher–Smith 14.7.11,49, printed pp.1045–1046,1064,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Quasithin.I5
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The A₆/S₆ full-quotient cases of original 14.7.11. The constructed
C₃ system has an elementary point core, contrary to the original plane
movement. All restrictions use the literal subgroupOf equivalence. -/
theorem small_local_alternatingSix_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hmovement : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (he : Nonempty (HStar I ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (HStar I ≃* Equiv.Perm (Fin 6))) : False := by
  obtain ⟨H₂,h₂,S,hS⟩ := small_local_source_system h hab structural previous faithful
    hmovement I hI .C3 (by simp) (fun _ => he)
  let E := (L ⊔ (T : Subgroup G)) ⊔ I
  have hS0 : S.family 0 = I.subgroupOf E := by rw [hS]; rfl
  let e := (MulEquiv.subgroupCongr hS0).trans
    (subgroupOfEquivOfLe (show I ≤ E from le_sup_right))
  let c := ((pCore 2 (S.family 0)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  let := c3_point_core_elementary S
  let : IsElementaryAbelian 2 (pCore 2 I) :=
    IsElementaryAbelian.of_surjective c.toMonoidHom c.surjective
  exact local_core_not_abelian_at h hab structural hmovement I hI inferInstance

/-- All three literal full-quotient exclusions in original 14.7.11. -/
theorem small_local_full_quotient_exclusions
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (core_commutator : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    ¬ Nonempty (HStar I ≃* Matrix.PSL3Two.PSL) ∧
      ¬ Nonempty (HStar I ≃* alternatingGroup (Fin 6)) ∧
      ¬ Nonempty (HStar I ≃* Equiv.Perm (Fin 6)) := by
  have hm := plane_moved_of_core_commutator h core_commutator
  exact ⟨small_local_linearThree_impossible h hab structural previous faithful hm I hI,
    fun he => small_local_alternatingSix_impossible h hab structural previous faithful hm I hI (Or.inl he),
    fun he => small_local_alternatingSix_impossible h hab structural previous faithful hm I hI (Or.inr he)⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
