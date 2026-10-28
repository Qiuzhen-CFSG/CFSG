module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Consumer
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.TwoPerfectCubicImages.SupportedCommutator
public import Theory.GroupTheory.PResidual.CommutatorImage

/-!
# The component and cubic Thompson-commutator branches

For the actual escaping Y and J = J_j(R), normalizer control already makes
[Y,J] escape O₂(Y). In the C-component branch, pass to the literal ambient
two-core quotient and use the ordinary component commutator dichotomy;
perfectness lifts generation back to Y. In the cubic branch, a normal
subgroup escaping O₂(Y) fills the simple quotient, and two-perfectness
removes the remaining two-group quotient. Both branches give K = Y = [K,J].

Consequently some member of the original Thompson family acts nontrivially
on D. The existing common action gives its actual B.2.4 fixed-codimension
bound. The candidate-overgroup application constructs all this on the same
Y and centralizer quotient. The original d > 3 alternative is retained.

This is progress toward 13.1.9, not its contradiction. Selection of the
controlled index, the larger odd-prime branch, common chief section, FF
inequality, tensor identification and final generation remain in
qt-d-1319-ff-contradiction. Earlier canonical geometry is discharged by
qt-d-1317-supplements and qt-d-1317-source in their final assembly.
Source: Aschbacher--Smith 13.1.9, printed pp.870--871.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin ChapterB
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Escape
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_twoPerfect [Group.IsPerfect G] : IsPPerfect 2 G := by
  intro N hN hp
  let := hN
  have hsub : Subsingleton (G ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem component_commutator_eq (Y J : Subgroup G)
    (hY : Y.IsCComponent) [IsQuasisimple (Y ⧸ pCore 2 Y)]
    (hn : J ≤ normalizer (Y : Set G)) (hm : ¬ ⁅Y,J⁆ ≤ Y.pCoreIn 2) :
    Y = ⁅Y,J⁆ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hq := QuotientGroup.mk'_surjective (pCore 2 G)
  have hc : IsComponent (G ⧸ pCore 2 G) (Y.map q) :=
    ⟨hY.subnormal.map hq, IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hY)⟩
  have hnq : J.map q ≤ normalizer (Y.map q : Set (G ⧸ pCore 2 G)) :=
    (map_mono hn).trans (Y.le_normalizer_map q)
  have hmq : ⁅Y.map q,J.map q⁆ ≠ ⊥ := by
    intro he
    have hle : ⁅Y,J⁆ ≤ pCore 2 G := by
      rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at he
      exact he
    exact hm (le_pCoreIn_of_normalizes (pCore_isPGroup.to_le hle)
      (le_normalizer_iff_commutator_le_left.mp hn) (normalizer_commutator_ge_left Y J))
  let := hY.perfect
  apply eq_commutator_of_isPPerfect_of_map_eq Y J perfect_twoPerfect hn q
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  have he := (hc.commutator_dichotomy (J.map q)).resolve_left hmq
  exact le_antisymm ((le_iSup_conjugates (Y.map q) (J.map q)).trans he.symm.le)
    (le_normalizer_iff_commutator_le_left.mp hnq)

variable {T : Sylow 2 G}
/-- The quasisimple two-core quotient forces K = Y in the component branch. -/
theorem component_thompson_commutator_eq {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hY : Y ∈ cComponentsIn H) (hq : IsQuasisimple (XiQuotient Y)) {j : ℕ}
    (hN : normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤
      normalizer (L : Set G)) :
    thompsonCommutator T L Y j = Y := by
  let R := radicalSylowCentralizer (T : Subgroup G) L
  let J := thompsonJ R j
  let Y₀ := Y.subgroupOf H
  let J₀ := J.subgroupOf H
  have hJH : J ≤ H := (thompsonJ_le R j).trans ((radicalSylowCentralizer_le T L).trans hTH)
  have hmY : Y₀.map H.subtype = Y := map_subgroupOf_eq_of_le hY.1
  have hmJ : J₀.map H.subtype = J := map_subgroupOf_eq_of_le hJH
  let e : Y₀ ≃* Y := subgroupOfEquivOfLe hY.1
  let eqv : (Y₀ ⧸ pCore 2 Y₀) ≃* (Y ⧸ pCore 2 Y) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := hq
  let : IsQuasisimple (Y₀ ⧸ pCore 2 Y₀) := IsQuasisimple.of_mulEquiv eqv.symm
  let : Y₀.Normal := w.witness.normal
  have hj := thompson_index_lt_of_normalizer_control Y R (normalizer (L : Set G))
    w.witness.outside hN
  have hncore := thompson_commutator_not_le_core Y R (normalizer (L : Set G))
    hj w.core_le w.witness.outside hN
  have hmove : ¬ ⁅Y₀,J₀⁆ ≤ Y₀.pCoreIn 2 := by
    intro hc
    have hh := map_mono (f := H.subtype) hc
    rw [map_commutator,hmY,hmJ] at hh
    apply hncore
    apply hh.trans_eq
    change ((pCore 2 Y₀).map Y₀.subtype).map H.subtype = (pCore 2 Y).map Y.subtype
    rw [map_map,show H.subtype.comp Y₀.subtype = Y.subtype.comp e.toMonoidHom from rfl,
      ← map_map,pCore_map_iso]
  have he := component_commutator_eq Y₀ J₀ hY.2 le_normalizer_of_normal hmove
  have hh := congrArg (map H.subtype) he
  rw [map_commutator,hmY,hmJ] at hh
  exact hh.symm


/-- In the cubic branch, two-perfectness removes the remaining two-group quotient. -/
theorem cubic_thompson_commutator_eq {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hp : IsPPerfect 2 Y) (hc : Nat.card (XiQuotient Y) = 3) {j : ℕ}
    (hN : normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤
      normalizer (L : Set G)) :
    thompsonCommutator T L Y j = Y := by
  let R := radicalSylowCentralizer (T : Subgroup G) L
  let J := thompsonJ R j
  let K := thompsonCommutator (T : Subgroup G) L Y j
  have hHY := (normal_subgroupOf_iff_le_normalizer w.witness.le_overgroup).mp w.witness.normal
  have hKY : K ≤ Y := le_normalizer_iff_commutator_le_left.mp
    ((thompsonJ_le R j).trans ((radicalSylowCentralizer_le T L).trans (hTH.trans hHY)))
  let : (K.subgroupOf Y).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left Y J)
  have hj := thompson_index_lt_of_normalizer_control Y R (normalizer (L : Set G))
    w.witness.outside hN
  have hnot := thompson_commutator_not_le_core Y R (normalizer (L : Set G))
    hj w.core_le w.witness.outside hN
  have hnot' : ¬ K.subgroupOf Y ≤ pCore 2 Y := by
    intro hh
    apply hnot
    intro k hk
    exact mem_map.mpr ⟨⟨k,hKY hk⟩,hh hk,rfl⟩
  have he := normal_eq_top_of_not_le_twoCore_cubic hp hc (K.subgroupOf Y) hnot'
  exact le_antisymm hKY (subgroupOf_eq_top.mp he)

/-- The refined source alternatives reduce K ≠ Y to the larger odd-prime branch. -/
theorem thompson_commutator_eq_or_large_odd {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H) {j : ℕ}
    (hN : normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤
      normalizer (L : Set G)) :
    thompsonCommutator T L Y j = Y ∨
      (IsPPerfect 2 Y ∧ ∃ d : ℕ, d.Prime ∧ 3 < d ∧ IsPGroup d (XiQuotient Y) ∧
        Monoid.exponent (XiQuotient Y) = d ∧ Group.nilpotencyClass (XiQuotient Y) ≤ 2) := by
  rcases w.refined with ⟨hY,hq,_⟩ | ⟨hp,⟨e⟩⟩ | ho
  · exact Or.inl (component_thompson_commutator_eq w hTH hY hq hN)
  · apply Or.inl
    apply cubic_thompson_commutator_eq w hTH hp _ hN
    exact (Nat.card_congr e.toEquiv).trans (by simp)
  · exact Or.inr ho

private theorem thompson_commutator_idempotent_of_eq {L Y : Subgroup G} {j : ℕ}
    (he : thompsonCommutator T L Y j = Y) :
    thompsonCommutator T L Y j =
      ⁅thompsonCommutator T L Y j,thompsonJ (radicalSylowCentralizer T L) j⁆ := by
  conv_rhs => rw [he]
  rfl


private theorem exists_hat_thompson_actor_of_idempotent (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    (hD : omegaClosure T L Y j ≤ commonGroup T L Y j)
    (hKD : thompsonCommutator T L Y j ≤ normalizer (omegaClosure T L Y j : Set G))
    (hm : hatImage T L Y j (thompsonCommutator T L Y j) ≠ ⊥)
    (hi : thompsonCommutator T L Y j =
      ⁅thompsonCommutator T L Y j,thompsonJ (radicalSylowCentralizer T L) j⁆) :
    ∃ A ∈ thompsonFamily (radicalSylowCentralizer T L) j, hatImage T L Y j A ≠ ⊥ := by
  let D := omegaClosure T L Y j
  let K := thompsonCommutator T L Y j
  let R := radicalSylowCentralizer T L
  by_contra! hn
  have hJC : thompsonJ R j ≤ centralizer (D : Set G) := by
    apply sSup_le
    intro A hA
    have ha : A ≤ commonGroup T L Y j := hA.1.trans (le_sup_right.trans le_sup_right)
    have hc := (hat_image_eq_bot_iff T L Y A j hD ha).mp (hn A hA)
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hkC : K ≤ centralizer (D : Set G) := by
    change thompsonCommutator T L Y j ≤ _
    rw [hi]
    exact (commutator_mono le_rfl hJC).trans
      (le_normalizer_iff_commutator_le_right.mp
        (hKD.trans (normalizer_le_normalizer_centralizer D)))
  apply hm
  apply (hat_image_eq_bot_iff T L Y K j hD (le_sup_left.trans le_sup_right)).mpr
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hkC

/-- The component and cubic branches have their actual Thompson actor;
only the original larger odd-prime alternative remains. -/
@[expose] def ThompsonActorAlternative (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)] : Prop :=
    (thompsonCommutator T L Y j = Y ∧
      thompsonCommutator T L Y j =
        ⁅thompsonCommutator T L Y j,thompsonJ (radicalSylowCentralizer T L) j⁆ ∧
      ∃ A ∈ thompsonFamily (radicalSylowCentralizer T L) j,
        hatImage T L Y j A ≠ ⊥ ∧ HatActorBound (T : Subgroup G) L Y A j) ∨
    (IsPPerfect 2 Y ∧ ∃ d : ℕ, d.Prime ∧ 3 < d ∧ IsPGroup d (XiQuotient Y) ∧
      Monoid.exponent (XiQuotient Y) = d ∧ Group.nilpotencyClass (XiQuotient Y) ≤ 2)

/-- Select a member of the actual Thompson family and retain its original action bound. -/
theorem common_action_actor_or_large_odd {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ}
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)]
    (hN : normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤
      normalizer (L : Set G))
    (ha : CommonActionProperties (T : Subgroup G) L Y j) :
    ThompsonActorAlternative (T : Subgroup G) L Y j := by
  rcases thompson_commutator_eq_or_large_odd w hTH hN with he | ho
  · have hi := thompson_commutator_idempotent_of_eq he
    have hd := omegaClosure_geometry w hTH hAH hTL j
    obtain ⟨A,hA,hAn⟩ := exists_hat_thompson_actor_of_idempotent (T : Subgroup G) L Y j
      (hd.2.1.trans le_sup_right) (le_sup_left.trans hd.2.2.1)
      ha.commutator_nontrivial hi
    exact Or.inl ⟨he,hi,A,hA,hAn,ha.actor_bound A hA hAn⟩
  · exact Or.inr ho

open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The actual candidate has a Thompson actor in the component and cubic
branches, with the literal common action and its B.2.4 bound. The larger
odd-prime branch and the controlled-index construction remain open. -/
theorem candidate_common_action_with_actor_alternative (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement T L ≤ C)
    {j : ℕ}
    (hN : normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤
      normalizer (L : Set G)) :
    ∃ Y : Subgroup G, RefinedWitness T L H C Y ∧
      ⁅⁅omegaClosure T L Y j,canonicalSupplement T L⁆,thompsonCommutator T L Y j⁆ ≠ ⊥ ∧
      ∃ n : (commonModule T L Y j).Normal,
        let := n
        ∃ e : IsElementaryAbelian 2 (commonModule T L Y j),
        let := e
        CommonActionProperties (T : Subgroup G) L Y j ∧
          ThompsonActorAlternative (T : Subgroup G) L Y j := by
  obtain ⟨Y,w,hm,n,he⟩ := candidate_common_action h hmany hs hrig hclass hL hn
    hH hTH hne hC hAC hN
  let := n
  obtain ⟨e,ha⟩ := he
  let := e
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  exact ⟨Y,w,hm,n,e,ha,common_action_actor_or_large_odd w hTH
    (hAC.trans hC.1) hTL hN ha⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
