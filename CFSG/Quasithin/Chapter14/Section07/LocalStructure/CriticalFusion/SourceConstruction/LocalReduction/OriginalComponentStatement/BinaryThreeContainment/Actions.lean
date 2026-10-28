module
public import Theory.SpecificGroups.PSL3Two.Automorphisms.SylowStabilizer
public import Theory.GroupTheory.CubicInverterInnerComponent
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneCubic

/-!
# The outside point action on a binary linear-three component

The original point residual outside a normal component preserves its actual
Sylow intersection. In SL3(2) the full automorphism stabilizer of a Sylow
two-subgroup is a two-group. Two-perfectness therefore kills the whole point
action on the intrinsic component quotient. The same quotient calculation
lifts to normalization of the original point residual.

The same-G,T application retains relative component normality. The original
all-component wrapper supplies it with the proved component normality theorem;
no use of 14.7.47 or of its later 14.7.49 exclusion is made.
Source: Aschbacher--Smith 14.7.47, printed p.1064, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment
variable {G : Type*} [Group G] [Finite G]

/-- The two-perfect outside cubic acts trivially on the full intrinsic quotient. -/
theorem outside_action_trivial
    (A C : Subgroup G) [C.Normal] (S : Sylow 2 G)
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hn : (S : Subgroup G) ≤ normalizer (A : Set G)) (hout : ¬ A ≤ C)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.SL) :
    A ≤ (normalQuotientAction C (pCore 2 C)).ker := by
  let E := A ⊔ (S : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let qE := e.toMonoidHom.comp q
  let a := normalQuotientAction C (pCore 2 C)
  let b := (MulAut.congr e).toMonoidHom.comp a
  have hEC : E ≤ normalizer (C : Set G) := le_normalizer_of_normal
  have hCE : IsPGroup 2 (C ⊓ E : Subgroup G) := by
    rw [inf_comm,cubic_supplement_inf_normal A C S hp hc hn hout]
    exact S.isPGroup'.to_le inf_le_left
  have hb (x : E) (c : C) : b x (qE c) =
      qE (C.normalizerMonoidHom ⟨x,hEC x.property⟩ c) := by
    change MulAut.congr e (a x) (e (q c)) = _
    simp only [MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply]
    change e (normalQuotientAction C (pCore 2 C) x
      (QuotientGroup.mk' (pCore 2 C) c)) = _
    rw [normalQuotientAction_apply_mk]
    rfl
  have hf := NormalSylowQuotientAction.pPerfect_action_eq_one S C E A
    hEC le_sup_right hCE le_sup_left hp qE
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (b.comp E.subtype) hb
    Matrix.PSL3Two.automorphism_sylow_stabilizer_two
  intro x hx
  have hh : b x = 1 := hf ⟨x,hx⟩
  exact (MulAut.congr e).injective (hh.trans (map_one (MulAut.congr e)).symm)

open Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

/-- The literal point action is trivial, and the component normalizes the
original point residual. Only structural input at the original G,T is used. -/
theorem local_outside_action_trivial_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL) :
    (F.Li L 1).subgroupOf I ≤ (normalQuotientAction C (pCore 2 C)).ker ∧
      C.map I.subtype ≤ normalizer (F.Li L 1 : Set G) := by
  let A := (F.Li L 1).subgroupOf I
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  have hAI := F.Li_one_le_of_mem_Hz hI
  let ea := subgroupOfEquivOfLe hAI
  have hp : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 _).of_surjective
    ea.symm.toMonoidHom ea.symm.surjective
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  have hn : (S : Subgroup I) ≤ normalizer (A : Set I) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (T_normalizes_L₁_at h structural hx) (a : G)
  have hnot : ¬ A ≤ C := by
    intro hh
    apply hout
    have hm := map_mono (f := I.subtype) hh
    rwa [map_subgroupOf_eq_of_le hAI] at hm
  have hfix := outside_action_trivial A C S hp hc hn hnot
    (e.trans Matrix.PSL3Two.equiv.symm)
  refine ⟨hfix,?_⟩
  have hnorm := (map_mono (f := I.subtype)
    (normalizes_of_trivial_core_action A C S hp hn hfix)).trans
      (A.le_normalizer_map I.subtype)
  rwa [map_subgroupOf_eq_of_le hAI] at hnorm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment
