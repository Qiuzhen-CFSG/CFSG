module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Movement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalOffender
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality

/-!
# Original point-core movement in the graph branch

An original local component with intrinsic quotient order greater than 168
embeds, modulo a two-group kernel, in the full point component. Thus the
point core moves the original plane. Its commutator with the original span
is then exactly the point. In particular the degree-four and degree-five
binary linear rows provide the commutator used by the graph-node argument.

Source: Aschbacher–Smith 14.7.4(3), 14.7.48 and 14.7.51, pp.1043,1064–1065.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open AlternatingSevenSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Large intrinsic quotient order in any original local forces point-core
movement of the original plane. -/
theorem local_large_component_plane_moved_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hlarge : 168 < Nat.card (C ⧸ pCore 2 C)) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  obtain ⟨D,hD,_,_⟩ := GuardedSource.local_exists_quasisimple_component
    d h hab structural previous faithful earlier F.H hH
  have hc := (local_component_eq_residual_at d h hab structural previous faithful earlier
    source47 I hI C hC).1
  have hd := (local_component_eq_residual_at d h hab structural previous faithful earlier
    source47 F.H hH D hD).1
  let i : I →* F.H := inclusion hI.2.1
  have hCD : C.map i ≤ D := by
    rw [←hc,←hd]
    exact map_pResidual_le 2 i
  let j : C →* D := (i.comp C.subtype).codRestrict D (fun c =>
    hCD (mem_map_of_mem i c.property))
  have hj : Function.Injective j := by
    intro a b he
    apply Subtype.ext
    apply inclusion_injective hI.2.1
    exact congrArg Subtype.val he
  let f := (QuotientGroup.mk' (pCore 2 D)).comp j
  have hk : IsPGroup 2 f.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective j hj
  have hdiv := f.pCoreQuotient_card_dvd_of_isPGroup_ker 2 hk
  apply plane_moved_of_large_component_at h structural previous faithful D hD
  exact hlarge.trans_le (Nat.le_of_dvd (Nat.card_pos (α := D ⧸ pCore 2 D)) hdiv)

/-- Plane movement makes the original span's core commutator equal to the
original point, whose order is two. -/
theorem core_commutator_eq_point_of_plane_moved
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥) :
    ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hle : ⁅F.U,F.H.pCoreIn 2⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact section_core_commutator_le_point h s
  have hne : ⁅F.U,F.H.pCoreIn 2⁆ ≠ ⊥ := by
    intro hz
    apply hm
    apply bot_unique
    rw [←hz]
    exact commutator_mono ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) le_rfl
  let A := ⁅F.U,F.H.pCoreIn 2⁆
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  let : Fact (Nat.card (F.Vi 1)).Prime := ⟨hcard.symm ▸ Nat.prime_two⟩
  have ht : A.subgroupOf (F.Vi 1) = ⊤ := by
    apply (A.subgroupOf (F.Vi 1)).eq_bot_or_eq_top_of_prime_card.resolve_left
    intro he
    apply hne
    have hm := congrArg (fun S : Subgroup (F.Vi 1) => S.map (F.Vi 1).subtype) he
    rwa [map_subgroupOf_eq_of_le hle,Subgroup.map_bot] at hm
  have hm := congrArg (fun S : Subgroup (F.Vi 1) => S.map (F.Vi 1).subtype) ht
  rwa [map_subgroupOf_eq_of_le hle,←MonoidHom.range_eq_map,range_subtype] at hm

/-- Both possible graph degrees supply point-core movement and the exact
core commutator, directly from the original component model. -/
theorem local_linear_graph_movement_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (n : ℕ) (hn : n = 4 ∨ n = 5)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ ∧ ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1 := by
  have hlarge : 168 < Nat.card (C ⧸ pCore 2 C) := by
    rw [Nat.card_congr e.toEquiv,BinaryLinear.card_SL]
    rcases hn with rfl | rfl <;> norm_num [BinaryLinear.order,Fin.prod_univ_succ]
  have hm := local_large_component_plane_moved_at d h hab structural previous faithful
    earlier source47 I hI C hC hlarge
  exact ⟨hm,core_commutator_eq_point_of_plane_moved h hab hm⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
