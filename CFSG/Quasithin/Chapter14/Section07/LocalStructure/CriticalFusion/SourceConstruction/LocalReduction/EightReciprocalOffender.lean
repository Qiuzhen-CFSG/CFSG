module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightTransvectionExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.CriticalActors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Selection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Offender
import Mathlib.Tactic

/-!
# The actual reciprocal offender in the original S₈ branch

The whole-section transvection exclusion detects elementary actors whose
commutators lie in a line: such actors lie in the literal O₂(H). Apply this
to the transported terminal edge of an original critical path. If its actor
had trivial star image, the reverse span would lie in the reverse two-core,
contradicting criticality. Thus the source actor is nontrivial, without a
rank-one or kernel-fixation assumption.

The original path reversal now selects the source rank comparison. On the
same U/V₁ section, the selected actor is quadratic and has a common
commutator line on U ∩ Qα. Its fixed codimension is at most twice its star
rank, and each element moves at most one plus the reciprocal index rank.
The final application constructs the canonical section with the same-G,T
many-overgroup guards used by the endgame.

A rank-one selected actor still moves exactly two dimensions on the whole
section; higher actor rank also remains possible in these estimates. This
module proves the reciprocal selection and its bounds, not their exclusion
or the full 14.7.51–52 classification. The generating seed and remaining
model reductions are still required.

Source: Aschbacher–Smith, 14.5.18(1–5), Notation 14.7.1 and the S₈ branch
of 14.7.51, printed pp.1018,1043,1065; F.9.16–17, pp.323–324.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- An elementary actor with displacement in a line dies in the actual star quotient. -/
theorem eight_actor_in_core_of_line_commutator_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8))
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (A C : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ F.H) (hc : ⁅A,F.U⁆ ≤ C) (hC : Nat.card C ≤ 2) :
    A ≤ F.H.pCoreIn 2 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  let D := s.imageSpace C
  have hDcard : Nat.card D ≤ 2 := by
    change Nat.card ((C.subgroupOf F.U).map s.coordinates) ≤ 2
    have hm := Nat.card_le_card_of_surjective (s.coordinates.subgroupMap
      (C.subgroupOf F.U)) (s.coordinates.subgroupMap_surjective _)
    have hs : Nat.card (C.subgroupOf F.U) ≤ Nat.card C :=
      Nat.card_le_card_of_injective (fun y => (⟨y.val,y.property⟩ : C))
        (by
          intro a b he
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : C => (z:G)) he)
    exact hm.trans (hs.trans hC)
  have hdim : Module.finrank (ZMod 2) D ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod] at hDcard
    by_contra hn
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show 2 ≤ Module.finrank (ZMod 2) D by omega)
    omega
  intro x hx
  let a : F.H := ⟨x,hA hx⟩
  have ha2 : a ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x hx)
  have hb : fixedCodim ρ (zpowers a) ≤ 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact (Submodule.finrank_mono (s.displacement_range_le_imageSpace_of_commutator_le
      A C hc a hx)).trans hdim
  have ha : starMap F a = 1 := by
    by_contra hn
    have h2 : starMap F a ^ 2 = 1 := by rw [←map_pow,ha2,map_one]
    have hno := original_eight_involution_fixedCodim_ne_one_at h structural previous faithful e s a hn h2
    have hz : fixedCodim ρ (zpowers a) = 0 := by omega
    have hfix := (fixedCodim_eq_zero_iff ρ (zpowers a)).mp hz
    have hak : a ∈ ρ.ker := by
      apply LinearMap.ext
      intro w
      have hw : w ∈ fixedSpace ρ (zpowers a) := hfix ▸ Submodule.mem_top
      exact hw ⟨a,mem_zpowers a⟩
    rw [original_eight_action_kernel_eq_core h e s] at hak
    exact hn ((QuotientGroup.eq_one_iff a).mpr hak)
  exact mem_map_of_mem F.H.subtype ((QuotientGroup.eq_one_iff a).mp ha)

/-- The actual critical actor survives, using terminal-edge transport and
whole-section transvection exclusion instead of an assumed rank-one actor. -/
theorem eight_critical_star_nontrivial_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8)) (c : CriticalPath (L := L) F) :
    star F c.Uα ≠ ⊥ := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  intro hz
  have hAH : c.Uα ≤ F.H := (critical_le_Q_at h structural c).trans (Q_le_H F)
  have hαQ : c.Uα ≤ F.H.pCoreIn 2 := by
    have hk : c.Uα.subgroupOf F.H ≤ pCore 2 F.H := by
      simpa only [CriticalFusion.Source.star,Subgroup.map_eq_bot_iff,starMap,QuotientGroup.ker_mk'] using hz
    intro x hx
    exact mem_map.mpr ⟨⟨x,hAH hx⟩,hk hx,rfl⟩
  have hcomm : ⁅F.U,c.Uα⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    have haH : a ∈ F.H := hAH ha
    have hqa : (⟨a,haH⟩ : F.H) ∈ pCore 2 F.H := by
      have hh := hαQ ha
      obtain ⟨a',ha',he⟩ := hh
      exact (show a' = ⟨a,haH⟩ from Subtype.ext he) ▸ ha'
    exact (s.action_mem_ker_iff ⟨a,haH⟩).mp (core_le_action_kernel h s hqa) u hu
  obtain ⟨g,hUg,hHg,hAR⟩ := exists_terminal_edge_transport_at h structural c
  let f := (MulAut.conj g).toMonoidHom
  let A := F.U.map f
  let C := (F.Vi 1).map f
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hc : ⁅A,F.U⁆ ≤ C := by
    have hm := map_mono (f:=f) hcomm
    change c.Uα.map f = F.U at hUg
    rw [map_commutator,hUg] at hm
    exact hm
  have hC : Nat.card C ≤ 2 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact (show Nat.card (F.Vi 1)=2 by simpa using F.card 1 (by decide)).le
  have hAQ := eight_actor_in_core_of_line_commutator_at h structural previous faithful e s A C
    (hAR.trans ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))) hc hC
  have hQmap : c.Qα.map f = F.H.pCoreIn 2 := by
    change ((conjugate F.H c.conjugator).pCoreIn 2).map f = _
    rw [map_pCoreIn_of_injective 2 _ f (MulAut.conj g).injective,hHg]
  apply critical_span_not_le_reciprocal_core c
  exact (map_le_map_iff_of_injective (f:=f) (MulAut.conj g).injective).mp
    (hAQ.trans_eq hQmap.symm)


/-- The reciprocal source construction selects the actual offender. Its
common displacement line lies in the original U ∩ Qα; no split kernel or
choice of a rank-one involution is assumed. -/
theorem exists_eight_selected_critical_action_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8))
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧
      c.Uα ≤ F.Ri L 1 ∧ star F c.Uα ≠ ⊥ ∧ F.Vi 1 ≤ c.Qα ∧
      IsQuadratic ρ (c.Uα.subgroupOf F.H) ∧
      ⁅c.Uα,F.U ⊓ c.Qα⁆ ≤ c.Zα ∧
      fixedCodim ρ (c.Uα.subgroupOf F.H) ≤ 2 * Nat.log 2 (Nat.card (star F c.Uα)) ∧
      (∀ a : F.H, (a:G) ∈ c.Uα →
        Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤
          Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) + 1) ∧
      (∀ a : F.H, (a:G) ∈ c.Uα → starMap F a ≠ 1 →
        2 ≤ Module.finrank (ZMod 2) (ρ a - LinearMap.id).range) := by
  obtain ⟨c⟩ := exists_criticalPath_at h hab (h.flag_escape_at F previous) structural
  obtain ⟨c,hsel⟩ := select_critical_orientation_of_nontrivial_star_at h structural c
    (eight_critical_star_nontrivial_at h hab structural previous faithful e c)
  have hk := original_eight_action_kernel_eq_core h e s
  obtain ⟨hb,hi⟩ := critical_fixedCodim_bounds_of_kernel_at h hab structural hk s c
  have hquad := critical_quadratic h hab s c
  have hcomm : ⁅c.Uα,F.U ⊓ c.Qα⁆ ≤ c.Zα := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_right le_rfl).trans
      (reciprocal_core_commutator_le_point h s c)
  refine ⟨c,hsel,critical_le_Ri_at h structural c,
    eight_critical_star_nontrivial_at h hab structural previous faithful e c,
    point_le_reciprocal_core_of_kernel_at h structural hk s c,hquad,hcomm,?_,hi,?_⟩
  · have := hsel.comparison
    omega
  · intro a ha hn
    let := h.chosen.elementary
    let := hab
    let := elementary_U F
    let : IsElementaryAbelian 2 c.Uα :=
      IsElementaryAbelian.map (MulAut.conj c.conjugator⁻¹).toMonoidHom
    let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
      (Multiplicative.toAdd.surjective.comp s.onto)
    have ha2 : a ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ ha)
    have ht2 : starMap F a ^ 2 = 1 := by rw [←map_pow,ha2,map_one]
    have hno := original_eight_involution_fixedCodim_ne_one_at h structural previous faithful e s a hn ht2
    have hpos : fixedCodim ρ (zpowers a) ≠ 0 := by
      intro hz
      have hfix := (fixedCodim_eq_zero_iff ρ (zpowers a)).mp hz
      have hak : a ∈ ρ.ker := by
        apply LinearMap.ext
        intro w
        have hw : w ∈ fixedSpace ρ (zpowers a) := hfix ▸ Submodule.mem_top
        exact hw ⟨a,mem_zpowers a⟩
      rw [hk] at hak
      exact hn ((QuotientGroup.eq_one_iff a).mpr hak)
    rw [fixedCodim_zpowers_eq_displacement_rank] at hno hpos
    omega

/-- In the rank-one critical case the reciprocal index has binary rank one and
 every nontrivial star element moves exactly two dimensions on the whole
 original section. The other alternative retains genuine higher actor rank. -/
theorem exists_eight_selected_critical_alternatives_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8))
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧
      c.Uα ≤ F.Ri L 1 ∧ star F c.Uα ≠ ⊥ ∧
      IsQuadratic ρ (c.Uα.subgroupOf F.H) ∧
      ⁅c.Uα,F.U ⊓ c.Qα⁆ ≤ c.Zα ∧
      fixedCodim ρ (c.Uα.subgroupOf F.H) ≤ 2 * Nat.log 2 (Nat.card (star F c.Uα)) ∧
      ((Nat.log 2 (Nat.card (star F c.Uα)) = 1 ∧
        Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) = 1 ∧
        ∀ a : F.H, (a:G) ∈ c.Uα → starMap F a ≠ 1 →
          Module.finrank (ZMod 2) (ρ a - LinearMap.id).range = 2) ∨
        2 ≤ Nat.log 2 (Nat.card (star F c.Uα))) := by
  obtain ⟨c,hs,hR,hn,_,hq,hc,hb,hi,hl⟩ :=
    exists_eight_selected_critical_action_at h hab structural previous faithful e s
  refine ⟨c,hs,hR,hn,hq,hc,hb,?_⟩
  have hp := hs.positive
  have hcmp := hs.comparison
  by_cases hk : Nat.log 2 (Nat.card (star F c.Uα)) = 1
  · left
    have hd : Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) = 1 := by omega
    refine ⟨hk,hd,?_⟩
    intro a ha hn
    have hu := hi a ha
    have hlo := hl a ha hn
    omega
  · right
    omega

/-- Apply the reciprocal construction to the canonical section, with the
same-G,T many-overgroup guards used by the endgame. -/
theorem exists_eight_selected_reciprocal_actor_of_many_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8)) :
    ∃ (E : Type u) (_ : AddCommGroup E) (_ : Module (ZMod 2) E)
      (σ : Representation (ZMod 2) F.H E),
      Nonempty (BinaryConjugationSection F.H F.U (F.Vi 1) σ) ∧
      ∃ c : CriticalPath (L := L) F, c.RankSelection ∧
        c.Uα ≤ F.Ri L 1 ∧ star F c.Uα ≠ ⊥ ∧
        IsQuadratic σ (c.Uα.subgroupOf F.H) ∧
        ⁅c.Uα,F.U ⊓ c.Qα⁆ ≤ c.Zα ∧
        fixedCodim σ (c.Uα.subgroupOf F.H) ≤ 2 * Nat.log 2 (Nat.card (star F c.Uα)) ∧
        ((Nat.log 2 (Nat.card (star F c.Uα)) = 1 ∧
          Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) = 1 ∧
          ∀ a : F.H, (a:G) ∈ c.Uα → starMap F a ≠ 1 →
            Module.finrank (ZMod 2) (σ a - LinearMap.id).range = 2) ∨
          2 ≤ Nat.log 2 (Nat.card (star F c.Uα))) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨σ,⟨s⟩⟩ := exists_section F
  exact ⟨_,inferInstance,inferInstance,σ,⟨s⟩,
    exists_eight_selected_critical_alternatives_at h hab (structural hmany)
      (previous hmany) faithful e s⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
